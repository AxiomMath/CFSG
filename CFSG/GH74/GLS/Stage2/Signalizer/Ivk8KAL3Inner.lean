module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Aut
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphThree

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.KGroups.L3Eps
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups

section Block

variable {F : Type} [Field F]

@[expose] noncomputable def kaL3U : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] noncomputable def kaL3L : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

@[expose] noncomputable def kaL3Tr (t : F) : SL(2, F) :=
  ⟨!![0, 1; -1, t], by simp [Matrix.det_fin_two]⟩

theorem kaL3_block_form (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 3) (Fin 3) F}
    (hcomm : ∀ B : SL(2, F), A * ((bSL B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((bSL B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * A) :
    A = !![A 0 0, 0, 0; 0, A 0 0, 0; 0, 0, A 2 2] := by
  have hd : A * ((dNeg : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((dNeg : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * A := by
    simpa [bSL_neg_one] using hcomm (-1)
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_commute_dNeg h2 hd
  have hu := hcomm kaL3U
  have hl := hcomm kaL3L
  rw [coe_bSL] at hu hl
  have u00 := congrFun (congrFun hu 0) 0
  have u01 := congrFun (congrFun hu 0) 1
  have l00 := congrFun (congrFun hl 0) 0
  simp [kaL3U, kaL3L, Matrix.mul_apply, Fin.sum_univ_three] at u00 u01 l00
  have h10 : A 1 0 = 0 := u00
  have h01 : A 0 1 = 0 := l00
  have h11 : A 1 1 = A 0 0 := by linear_combination -u01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21, h10, h01, h11]

@[expose] noncomputable def kaTorusGL (c : Fˣ) : GL (Fin 3) F where
  val := Matrix.diagonal ![(c : F), (c : F), 1]
  inv := Matrix.diagonal ![((c⁻¹ : Fˣ) : F), ((c⁻¹ : Fˣ) : F), 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem coe_kaTorusGL (c : Fˣ) :
    ((kaTorusGL c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(c : F), (c : F), 1] := rfl

@[expose] noncomputable def kaTorus : Fˣ →* GL (Fin 3) F where
  toFun := kaTorusGL
  map_one' := by
    apply Units.ext
    rw [coe_kaTorusGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Units.ext
    rw [Units.val_mul, coe_kaTorusGL, coe_kaTorusGL, coe_kaTorusGL, Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem kaL3_fix_block [Finite F] (h2 : (2 : F) ≠ 0)
    (hlift : ∀ (A : GL (Fin 3) F) (σ : F ≃+* F),
      (∀ g ∈ (bSL : SL(2, F) →* SL(3, F)).range, proj 3 F (semiSL A σ g) = proj 3 F g) →
        ∀ g ∈ (bSL : SL(2, F) →* SL(3, F)).range, semiSL A σ g = g)
    {β : MulAut (projectiveSL 3 F)} {m : ℕ} (hm : Odd m) (hβ : β ^ m = 1)
    (hfix : ∀ r ∈ (blockSub : Subgroup (projectiveSL 3 F)), β r = r) :
    ∃ c : Fˣ, β = conjAut 3 F (kaTorusGL c) := by
  obtain ⟨A, σ, rfl, -⟩ := kaL3_pow_semilinear hm hβ
  have hf1 : ∀ g ∈ (bSL : SL(2, F) →* SL(3, F)).range, semiSL A σ g = g := by
    refine hlift A σ fun g hg => ?_
    rw [← beta_proj]
    obtain ⟨B, rfl⟩ := hg
    exact hfix (proj 3 F (bSL B)) ⟨B, rfl⟩
  have hσ : σ = 1 := by
    ext t
    have h1 := hf1 (bSL (kaL3Tr t)) ⟨kaL3Tr t, rfl⟩
    have h2' := trace_semiSL A σ (bSL (kaL3Tr t))
    rw [h1] at h2'
    have h3 : Matrix.trace ((bSL (kaL3Tr t) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = t + 1 := by
      rw [Matrix.trace_fin_three, coe_bSL]
      simp [kaL3Tr]
    rw [h3, map_add, map_one] at h2'
    have h4 : σ t = t := by linear_combination -h2'
    simpa using h4
  subst hσ
  have hAcomm : ∀ B : SL(2, F), (A : Matrix (Fin 3) (Fin 3) F) *
      ((bSL B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((bSL B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * A := by
    intro B
    have h1 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F))
      (hf1 (bSL B) ⟨B, rfl⟩)
    simp only [coe_semiSL] at h1
    have h2'' : ((bSL B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map ⇑(1 : F ≃+* F) =
        ((bSL B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
      ext i j
      rfl
    rw [h2''] at h1
    have h3 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
        1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (A : Matrix (Fin 3) (Fin 3) F) * ((bSL B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
        = (A : Matrix (Fin 3) (Fin 3) F) * ((bSL B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
            ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
              (A : Matrix (Fin 3) (Fin 3) F) := by
          rw [Matrix.mul_assoc _ _ (A : Matrix (Fin 3) (Fin 3) F), h3, Matrix.mul_one]
      _ = ((bSL B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * A := by rw [h1]
  have hform := kaL3_block_form h2 hAcomm
  have hdet : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det A).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hsd : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
    constructor <;> intro h <;> apply hdet <;> rw [hform, Matrix.det_fin_three] <;> simp [h]
  obtain ⟨hs, hd⟩ := hsd
  set s := (A : Matrix (Fin 3) (Fin 3) F) 0 0 with hsdef
  set d := (A : Matrix (Fin 3) (Fin 3) F) 2 2 with hddef
  refine ⟨Units.mk0 (s / d) (div_ne_zero hs hd), ?_⟩
  have hA : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 d hd) *
      kaTorusGL (Units.mk0 (s / d) (div_ne_zero hs hd)) := by
    apply Units.ext
    rw [Units.val_mul, coe_kaTorusGL, hform]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply,
        mul_div_cancel₀ _ hd]
  rw [hA, map_mul, conjAut_scalar, one_mul, map_one, mul_one]

theorem kaL3_isCyclic_of_le {K : Type} [Group K] {A B : Subgroup K} [IsCyclic ↥B] (h : A ≤ B) :
    IsCyclic ↥A := by
  have : IsCyclic ↥(A.subgroupOf B) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
    fun a => ⟨(Subgroup.subgroupOfEquivOfLe h).symm a,
      (Subgroup.subgroupOfEquivOfLe h).apply_symm_apply a⟩

theorem kaL3_two_ne_zero [Finite F] (h : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  intro h2
  have : Fintype F := Fintype.ofFinite F
  have hc : ((2 : ℕ) : F) = 0 := by exact_mod_cast h2
  have hdvd : ringChar F ∣ 2 := (ringChar.spec F 2).mp hc
  have hp : ringChar F = 2 := by
    have hpr : (ringChar F).Prime := CharP.prime_ringChar F
    exact (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp hdvd
  have h0 : Fintype.card F % 2 = 0 := FiniteField.even_card_iff_char_two.mp hp
  rw [← Nat.card_eq_fintype_card] at h0
  have h1 := Nat.odd_iff.mp h
  omega

theorem ka_fixSub_conj_eq_centralizer {Y : Type} [Group Y] (u : Y) :
    fixSub (MulAut.conj u) = centralizer ({u} : Set Y) := by
  ext x
  rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff]
  show MulAut.conj u x = x ↔ x * u = u * x
  rw [MulAut.conj_apply]
  constructor
  · intro h
    have := congrArg (fun z => z * u) h
    simpa [mul_assoc] using this.symm
  · intro h
    rw [← h]
    group

theorem kaL3_mem_normalizer_blockSub (h2 : (2 : F) ≠ 0) {x : projectiveSL 3 F}
    (hx : x ∈ centralizer ({tInv} : Set (projectiveSL 3 F))) :
    x ∈ normalizer ((blockSub : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact fun hs => conj_mem_blockSub h2 hx hs
  · intro hs
    have h := conj_mem_blockSub h2 (Subgroup.inv_mem _ hx) hs
    have e : x⁻¹ * (x * s * x⁻¹) * x⁻¹⁻¹ = s := by group
    rwa [e] at h

section InnerFive

variable {F : Type} [Field F] [Finite F]

theorem kaL3_inner_five (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    KAAll (MulAut.conj (tInv : projectiveSL 3 F)) := by
  have h2 : (2 : F) ≠ 0 := kaL3_two_ne_zero hodd
  have h4 : 4 ≤ Nat.card F := by omega
  have hq : CFSG.IsQuasisimple SL(2, F) := isQuasisimple_sl2c h4
  have hbq : CFSG.IsQuasisimple ↥(blockSub : Subgroup (projectiveSL 3 F)) :=
    isQuasisimple_blockSub h4
  have hfixSub := ka_fixSub_conj_eq_centralizer (tInv : projectiveSL 3 F)
  have : Group.IsPerfect SL(2, F) := hq.1
  have hperfΩ : Group.IsPerfect ↥((bSL : SL(2, F) →* SL(3, F)).range) :=
    Group.IsPerfect.range bSL
  refine ka_all_of_torus_fix (ka_conj_injective_of_center_bot center_projectiveSL_three_eq_bot)
    (fixSub (MulAut.conj (tInv : projectiveSL 3 F))) (blockSub : Subgroup (projectiveSL 3 F))
    le_rfl (fun c hc _ => hc) (by rw [hfixSub]; exact blockSub_le_centralizer)
    (fun x hx => kaL3_mem_normalizer_blockSub h2 (by rwa [hfixSub] at hx))
    (Subgroup.isPerfect_iff.mp hbq.1) ?_ ?_ (fun x => ka_comm_mem_innSub tInv x)
  · intro p hp hp2 M hML hMp hMn
    exact ka_central_of_quasisimple_image (blockEmb : SL(2, F) →* projectiveSL 3 F) hq hp M hML
      hMp hMn
  · intro p hp hp2 P' hP' hfix
    have : Fact p.Prime := ⟨hp⟩
    let T : Fˣ →* MulAut (projectiveSL 3 F) := (conjAut 3 F).comp kaTorus
    have hle : P' ≤ T.range := by
      intro e he
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP') ⟨e, he⟩
      rw [Subgroup.orderOf_mk] at hm
      have hodd' : Odd (p ^ m) := (hp.odd_of_ne_two hp2).pow
      have hβ : e ^ (p ^ m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one e
      obtain ⟨c, hc⟩ := kaL3_fix_block h2
        (fun A σ h => semiSL_fix_of_perfect A σ hperfΩ h) hodd' hβ (fun r hr => hfix e he r hr)
      exact ⟨c, hc.symm⟩
    have : IsCyclic ↥T.range := isCyclic_of_surjective T.rangeRestrict
      (MonoidHom.rangeRestrict_surjective T)
    exact kaL3_isCyclic_of_le hle

end InnerFive

end Block

section InnerThree

variable {F : Type} [Field F] [Finite F]

theorem kaL3_eq_one_or_neg_of_card_three (hK : Nat.card F = 3) {x : F} (hx : x ≠ 0) :
    x = 1 ∨ x = -1 := by
  have : Fintype F := Fintype.ofFinite F
  have h1 : x ^ Fintype.card F = x := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, hK] at h1
  have h2 : x * (x * x - 1) = 0 := by linear_combination h1
  have h3 : x * x = 1 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hx
    · linear_combination h
  exact mul_self_eq_one_iff.mp h3

theorem kaL3_blockSub_gen_odd (hK : Nat.card F = 3) :
    Subgroup.closure {x : projectiveSL 3 F | x ∈ (blockSub : Subgroup (projectiveSL 3 F)) ∧
      Odd (orderOf x)} = blockSub := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  · rintro _ ⟨B, rfl⟩
    have hB : B ∈ Subgroup.closure {y : SL(2, F) | orderOf y = 3} := by
      rw [CFSG.LieType.HighestRoot.closure_orderOf_three_eq_top hK]
      exact Subgroup.mem_top B
    induction hB using Subgroup.closure_induction with
    | mem y hy =>
      refine Subgroup.subset_closure ⟨blockEmb_mem y, ?_⟩
      have hd : orderOf (blockEmb y) ∣ orderOf y := orderOf_map_dvd blockEmb y
      rw [hy] at hd
      exact Odd.of_dvd_nat (by decide) hd
    | one =>
      rw [map_one]
      exact one_mem _
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
    | inv a _ ha =>
      rw [map_inv]
      exact inv_mem ha

theorem kaL3_blockSub_O_p (hK : Nat.card F = 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M : Subgroup (projectiveSL 3 F)} (hMp : IsPGroup p ↥M)
    (hML : M ≤ (blockSub : Subgroup (projectiveSL 3 F)))
    (hMn : ∀ l ∈ (blockSub : Subgroup (projectiveSL 3 F)),
      l ∈ normalizer (M : Set (projectiveSL 3 F))) : M = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  let e : ↥(blockSub : Subgroup (projectiveSL 3 F)) ≃* SL(2, F) :=
    (MonoidHom.ofInjective (blockEmb_injective (F := F))).symm
  set N : Subgroup ↥(blockSub : Subgroup (projectiveSL 3 F)) := M.subgroupOf blockSub with hNdef
  have hN : N.Normal := ⟨fun n hn g => by
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hMn g g.2) n).mp hn
    simpa using this⟩
  have hNcard : Nat.card N = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hML).toEquiv
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hMp
  have hNodd : Nat.card N % 2 = 1 := by
    rw [hNcard, hk]
    exact Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  by_cases hNZ : N ≤ Subgroup.center ↥(blockSub : Subgroup (projectiveSL 3 F))
  · rw [eq_bot_iff]
    intro x hx
    have hxN : (⟨x, hML hx⟩ : ↥(blockSub : Subgroup (projectiveSL 3 F))) ∈ N :=
      Subgroup.mem_subgroupOf.mpr hx
    rcases blockSub_center (hNZ hxN) with h | h
    · rw [Subgroup.mem_bot]
      exact h
    · exfalso
      have hxodd : Odd (orderOf x) := by
        obtain ⟨m, hm⟩ := hMp ⟨x, hx⟩
        have hd : orderOf (⟨x, hx⟩ : ↥M) ∣ p ^ m := orderOf_dvd_of_pow_eq_one hm
        rw [Subgroup.orderOf_mk] at hd
        exact Odd.of_dvd_nat ((hp.odd_of_ne_two hp2).pow) hd
      have h2 : (2 : F) ≠ 0 := kaL3_two_ne_zero (by rw [hK]; decide)
      have hx2 : orderOf x = 2 := by
        have h' : x = tInv := h
        rw [h']
        exact orderOf_eq_prime (by rw [pow_two]; exact tInv_mul_self) (tInv_ne_one h2)
      rw [hx2] at hxodd
      exact (Nat.not_odd_iff_even.mpr even_two) hxodd
  · exfalso
    have h8 := CFSG.LieType.HighestRoot.eight_le_card_of_normal hK e N hNZ
    have h24 := CFSG.LieType.HighestRoot.card_eq_24 hK e
    have hdvd : Nat.card N ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card N
    have hle : Nat.card N ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card N = n at hdvd h8 hNodd hle
    interval_cases n <;> omega

theorem kaL3_centralizer_blockSub_three (hK : Nat.card F = 3) {y : projectiveSL 3 F}
    (hy : ∀ s ∈ (blockSub : Subgroup (projectiveSL 3 F)), y * s = s * y) : y = 1 ∨ y = tInv := by
  have h2 : (2 : F) ≠ 0 := kaL3_two_ne_zero (by rw [hK]; decide)
  obtain ⟨g, rfl⟩ := proj_surjective 3 F y
  have hZ : scalars 3 F = ⊥ := fl3g_scalars_eq_bot_of_card_three hK
  have hcomm : ∀ B : SL(2, F), (g : Matrix (Fin 3) (Fin 3) F) *
      ((bSL B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((bSL B : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * g := by
    intro B
    have h1 := hy (blockEmb B) ⟨B, rfl⟩
    rw [blockEmb_apply, ← map_mul, ← map_mul] at h1
    have h3 := proj_eq_proj_iff.1 h1
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h3
    have h4 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) h3
    simpa using h4
  have hform := kaL3_block_form h2 hcomm
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := g.2
  rw [hform, Matrix.det_fin_three] at hdet
  simp at hdet
  have hs : (g : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
  have hgs : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
    rcases kaL3_eq_one_or_neg_of_card_three hK hs with h | h
    · rw [h] at hdet
      linear_combination hdet
    · rw [h] at hdet
      linear_combination hdet
  rcases kaL3_eq_one_or_neg_of_card_three hK hs with h | h
  · left
    have : g = 1 := by
      apply Subtype.ext
      rw [hform, h, hgs]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [this, map_one]
  · right
    have : g = dNeg := by
      apply Subtype.ext
      rw [hform, h, hgs, coe_dNeg]
    rw [this]
    rfl

theorem kaL3_inner_three (hK : Nat.card F = 3) :
    KAAll (MulAut.conj (tInv : projectiveSL 3 F)) := by
  have h2 : (2 : F) ≠ 0 := kaL3_two_ne_zero (by rw [hK]; decide)
  have hfixSub := ka_fixSub_conj_eq_centralizer (tInv : projectiveSL 3 F)
  have hZ : scalars 3 F = ⊥ := fl3g_scalars_eq_bot_of_card_three hK
  refine ka_all_of_X0_bot (ka_conj_injective_of_center_bot center_projectiveSL_three_eq_bot)
    (blockSub : Subgroup (projectiveSL 3 F)) ?_ (kaL3_blockSub_gen_odd hK) ?_ ?_
  · rw [hfixSub]
    exact blockSub_le_centralizer
  · intro p hp hp2 X hXC hXp hXn
    have hXL : X ⊓ (blockSub : Subgroup (projectiveSL 3 F)) = ⊥ := by
      refine kaL3_blockSub_O_p hK hp hp2 (hXp.to_le inf_le_left) inf_le_right ?_
      intro l hl
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hXn l hl, Subgroup.le_normalizer hl⟩
    have hc : ∀ x ∈ X, ∀ s ∈ (blockSub : Subgroup (projectiveSL 3 F)), x * s = s * x := by
      intro x hx s hs
      have hxN := kaL3_mem_normalizer_blockSub h2 (by rw [← hfixSub]; exact hXC hx)
      have h1 : s * x⁻¹ * s⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hXn s hs) x⁻¹).mp (X.inv_mem hx)
      have h3 : x * s * x⁻¹ ∈ (blockSub : Subgroup (projectiveSL 3 F)) :=
        (Subgroup.mem_normalizer_iff.mp hxN s).mp hs
      have h4 : x * s * x⁻¹ * s⁻¹ ∈ X ⊓ (blockSub : Subgroup (projectiveSL 3 F)) := by
        refine ⟨?_, Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ hs)⟩
        have := X.mul_mem hx h1
        simpa [mul_assoc] using this
      rw [hXL, Subgroup.mem_bot] at h4
      calc x * s = (x * s * x⁻¹ * s⁻¹) * (s * x) := by group
        _ = s * x := by rw [h4, one_mul]
    rw [eq_bot_iff]
    intro x hx
    have hxodd : Odd (orderOf x) := ka_odd_of_mem_pGroup hp hp2 hXp hx
    rcases kaL3_centralizer_blockSub_three hK (fun s hs => hc x hx s hs) with h | h
    · rw [Subgroup.mem_bot]
      exact h
    · exfalso
      have hx2 : orderOf x = 2 := by
        rw [h]
        exact orderOf_eq_prime (by rw [pow_two]; exact tInv_mul_self) (tInv_ne_one h2)
      rw [hx2] at hxodd
      exact (Nat.not_odd_iff_even.mpr even_two) hxodd
  · intro p hp hp2 e hord hfix
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hord) ⟨e, Subgroup.mem_zpowers e⟩
    rw [Subgroup.orderOf_mk] at hm
    have hodd' : Odd (p ^ m) := (hp.odd_of_ne_two hp2).pow
    have hβ : e ^ (p ^ m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one e
    obtain ⟨c, hc⟩ := kaL3_fix_block h2 (fun A σ h => semiSL_fix_of_center_bot A σ hZ h) hodd' hβ
      (fun r hr => hfix r hr)
    have hc2 : c ^ 2 = 1 := by
      have := kaL3_eq_one_or_neg_of_card_three hK c.ne_zero
      apply Units.ext
      rcases this with h | h <;> simp [h]
    have he2 : e ^ 2 = 1 := by
      rw [hc]
      show ((conjAut 3 F) (kaTorus c)) ^ 2 = 1
      rw [← map_pow, ← map_pow, hc2, map_one, map_one]
    have hd1 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one he2
    have hd2 : orderOf e ∣ p ^ m := orderOf_dvd_of_pow_eq_one hβ
    have hcop : Nat.Coprime 2 (p ^ m) :=
      Nat.Coprime.pow_right m ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)

end InnerThree

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
