module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320SLRed
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.HardMathSupport.Solomon.Coordinator (c25Fix)
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine (rSL coe_rSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (diagGL coe_diagGL)

local notation "conjAut'" => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut
local notation "slConj" => CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation

variable {k : Type} [Field k]

theorem slConj_eq_of_comm (B : GL (Fin 3) k) (g : SpecialLinearGroup (Fin 3) k)
    (h : (B : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) =
      (g : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k)) : slConj 3 k B g = g := by
  apply Subtype.ext
  rw [coe_slConjugation, h, Matrix.mul_assoc]
  have : (B : Matrix (Fin 3) (Fin 3) k) * ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [this, Matrix.mul_one]

theorem comm_of_slConj_eq (B : GL (Fin 3) k) (g : SpecialLinearGroup (Fin 3) k)
    (h : slConj 3 k B g = g) : (B : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) =
      (1 : k) • ((g : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k)) := by
  have h1 : ((slConj 3 k B g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      (g : Matrix (Fin 3) (Fin 3) k) := by rw [h]
  rw [coe_slConjugation] at h1
  have hBB : ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [one_smul]
  calc (B : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k)
      = ((B : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) *
          ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) * (B : Matrix (Fin 3) (Fin 3) k) := by
        rw [Matrix.mul_assoc _ ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k), hBB, Matrix.mul_one]
    _ = (g : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k) := by rw [h1]

section

variable (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)

theorem mem_lift {M' : Subgroup (MulAut (SpecialLinearGroup (Fin 3) k))} {i : Fin 4}
    (hM : M'.map (descendAut 3 k) = pglSylowMax u i) {m : MulAut (SpecialLinearGroup (Fin 3) k)}
    (hm : descendAut 3 k m ∈ pglSylowMax u i) : m ∈ M' := by
  rw [← hM] at hm
  obtain ⟨m', hm', hmm⟩ := hm
  have := CFSG.Quasithin.G11.P4SL34.descendAut_injective k hmm
  rwa [← this]

theorem lift_card {M' : Subgroup (MulAut (SpecialLinearGroup (Fin 3) k))} {i : Fin 4}
    (hM : M'.map (descendAut 3 k) = pglSylowMax u i) :
    Nat.card M' = Nat.card (pglSylowMax u i) := by
  rw [← hM, Subgroup.card_map_of_injective (CFSG.Quasithin.G11.P4SL34.descendAut_injective k)]

theorem lift_stable (hk : Nat.card k = 4) (hu : u ≠ 1)
    {M' : Subgroup (MulAut (SpecialLinearGroup (Fin 3) k))} {i : Fin 4} (hi : i = 0 ∨ i = 2)
    (hM : M'.map (descendAut 3 k) = pglSylowMax u i) :
    M'.map (MulAut.congr (MulAut.conj (rSL : SpecialLinearGroup (Fin 3) k))).toMonoidHom = M' := by
  have hDinj := CFSG.Quasithin.G11.P4SL34.descendAut_injective k
  have hle : M'.map (MulAut.congr (MulAut.conj (rSL : SpecialLinearGroup (Fin 3) k))).toMonoidHom ≤
      M' := by
    rintro _ ⟨m, hm, rfl⟩
    apply mem_lift hM
    have hDm : descendAut 3 k m ∈ pglSylowMax u i := hM ▸ ⟨m, hm, rfl⟩
    have hy := map_congr_yInn_eq hk hu i hi
    have : descendAut 3 k ((MulAut.congr (MulAut.conj (rSL : SpecialLinearGroup (Fin 3) k)))
        m) = (MulAut.congr (yInn : MulAut (projectiveSL 3 k))) (descendAut 3 k m) := by
      rw [congr_apply_eq, congr_apply_eq, map_mul, map_mul, map_inv, descend_conj]
      rfl
    rw [MulEquiv.coe_toMonoidHom, this]
    rw [← hy]
    exact ⟨_, hDm, rfl⟩
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have : Finite (MulAut (SpecialLinearGroup (Fin 3) k)) :=
    Finite.of_injective (fun e : MulAut (SpecialLinearGroup (Fin 3) k) =>
      (e : SpecialLinearGroup (Fin 3) k → SpecialLinearGroup (Fin 3) k)) DFunLike.coe_injective
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.congr _).injective]

theorem goodGamma_lift_stable (hk : Nat.card k = 4) (hu : u ≠ 1)
    {M' : Subgroup (MulAut (SpecialLinearGroup (Fin 3) k))} {i : Fin 4} (hi : i = 0 ∨ i = 2)
    (hM : M'.map (descendAut 3 k) = pglSylowMax u i) :
    ∀ w ∈ goodGamma M', (rSL : SpecialLinearGroup (Fin 3) k) * w * rSL⁻¹ ∈ goodGamma M' := by
  intro w hw
  have := map_goodGamma_le (MulAut.conj (rSL : SpecialLinearGroup (Fin 3) k)) M'
  rw [lift_stable hk hu hi hM] at this
  exact this ⟨w, hw, rfl⟩

theorem a5_piece_sl (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    NormalSimple (c25Fix (Subgroup.zpowers (slConj 3 k (diagGL u))))
      (iota : SpecialLinearGroup (Fin 2) k →* _).range := by
  have hω0 : (u : k) ≠ 0 := u.ne_zero
  have hω1 : (u : k) ≠ 1 := val_ne_one hu
  let e : (iota : SpecialLinearGroup (Fin 2) k →* _).range ≃* SpecialLinearGroup (Fin 2) k :=
    (MonoidHom.ofInjective iota_injective).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨h, rfl⟩
    rw [mem_c25Fix_zpowers_iff]
    exact slConj_eq_of_comm (diagGL u) (iota h) (by rw [coe_diagGL_eq]; exact Dm_comm_iota _ h)
  · intro x hx n hn
    have hfix : slConj 3 k (diagGL u) x = x := (mem_c25Fix_zpowers_iff _ _).1 hx
    have hc := comm_of_slConj_eq _ _ hfix
    rw [coe_diagGL_eq] at hc
    obtain ⟨-, hblock⟩ := block_of_comm hω0 hω1 hc
    obtain ⟨h, rfl⟩ := hn
    exact conj_mem_range_iota hblock h
  · exact (MulEquiv.isSimpleGroup_congr e).2 (CFSG.Quasithin.H13.KGL34P.isSimpleGroup_sl_two hk)
  · obtain ⟨a, b, hab⟩ := sl2_noncomm (k := k)
    refine ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  · rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H13.KGL34P.card_sl_two hk]
    norm_num

theorem tau_piece_sl (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    have := LinearFieldFour.charP_two_of_card_eq_four hk
    NormalPrime (c25Fix (Subgroup.zpowers (slConj 3 k (Bgl u))))
      (Subgroup.zpowers (tau0 (val_mul_self_add hk hu))) := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  set hω : (u : k) * u + u + 1 = 0 := val_mul_self_add hk hu with hωdef
  set t := tau0 hω with ht
  have key : ∀ y ∈ c25Fix (Subgroup.zpowers (slConj 3 k (Bgl u))), y⁻¹ * t * y ∈ Subgroup.zpowers t := by
    intro g hg
    have hfix : slConj 3 k (Bgl u) g = g := (mem_c25Fix_zpowers_iff _ _).1 hg
    have hc := comm_of_slConj_eq _ _ hfix
    rw [coe_Bgl] at hc
    obtain ⟨e, he⟩ := tau_mul_conj hω (Or.inl rfl) hc
    have he' : tau0 hω * g = g * tau0 hω ^ e := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_pow, coe_tau0]
      exact he
    have : g⁻¹ * tau0 hω * g = tau0 hω ^ e := by
      rw [mul_assoc, he', inv_mul_cancel_left]
    refine ⟨(e : ℤ), ?_⟩
    show t ^ (e : ℤ) = _
    rw [zpow_natCast, ht, ← this]
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le, mem_c25Fix_zpowers_iff]
    refine slConj_eq_of_comm (Bgl u) (tau0 hω) ?_
    rw [coe_Bgl, coe_tau0]
    exact Mm_comm_tauM0 hω
  · intro x hx n hn
    have hle : Subgroup.zpowers t ≤ (Subgroup.zpowers t).comap (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.zpowers_le]
      have := key x⁻¹ (inv_mem hx)
      simpa [MulAut.conj_apply] using this
    have := hle hn
    simpa [MulAut.conj_apply] using this
  · have h7 : t ^ 7 = 1 := tau0_pow_seven hω
    have hdvd : Nat.card (Subgroup.zpowers t) ∣ 7 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one h7
    exact (by norm_num : Nat.Coprime 3 7).coprime_dvd_right hdvd

theorem top_le_goodGamma_sl_M0 (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
    {M' : Subgroup (MulAut (SpecialLinearGroup (Fin 3) k))}
    (hM : M'.map (descendAut 3 k) = pglSylowMax u 0) : ⊤ ≤ goodGamma M' := by
  have hDinj := CFSG.Quasithin.G11.P4SL34.descendAut_injective k
  have hs : slConj 3 k (diagGL u) ∈ M' := by
    refine mem_lift hM ?_
    rw [descend_slConj]
    exact xDiag_mem_M0 (k := k) (u := u)
  have hS : Subgroup.zpowers (slConj 3 k (diagGL u)) ≤ M' := by
    rw [Subgroup.zpowers_le]; exact hs
  have hSc : Nat.card (Subgroup.zpowers (slConj 3 k (diagGL u))) = 3 := by
    rw [Nat.card_zpowers, ← orderOf_injective _ hDinj, descend_slConj]
    exact orderOf_xDiag hk hu
  have hM9 : Nat.card M' = 9 := (lift_card hM).trans (card_pglSylowMax hk hu 0)
  have hL : (iota : SpecialLinearGroup (Fin 2) k →* _).range ≤ goodGamma M' :=
    le_goodGamma hS (by rw [hM9, hSc]) (Or.inr (a5_piece_sl hk hu))
  have := eq_top_of_x12 (goodGamma M') (goodGamma_lift_stable hk hu (Or.inl rfl) hM)
    (fun c => hL ⟨sl2x c, iota_sl2x c⟩)
  exact le_of_eq this.symm

theorem top_le_goodGamma_sl_M2 (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
    {M' : Subgroup (MulAut (SpecialLinearGroup (Fin 3) k))}
    (hM : M'.map (descendAut 3 k) = pglSylowMax u 2) : ⊤ ≤ goodGamma M' := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hDinj := CFSG.Quasithin.G11.P4SL34.descendAut_injective k
  have hs : slConj 3 k (Bgl u) ∈ M' := by
    refine mem_lift hM ?_
    rw [descend_slConj, ← xDiag_mul_yInn]
    exact xDiag_mul_yInn_mem_M2 (k := k) (u := u)
  have hS : Subgroup.zpowers (slConj 3 k (Bgl u)) ≤ M' := by
    rw [Subgroup.zpowers_le]; exact hs
  have hSc : Nat.card (Subgroup.zpowers (slConj 3 k (Bgl u))) = 3 := by
    rw [Nat.card_zpowers, ← orderOf_injective _ hDinj, descend_slConj, ← xDiag_mul_yInn]
    exact orderOf_xDiag_mul_yInn hk hu
  have hM9 : Nat.card M' = 9 := (lift_card hM).trans (card_pglSylowMax hk hu 2)
  set hω : (u : k) * u + u + 1 = 0 := val_mul_self_add hk hu with hωdef
  have hN : Subgroup.zpowers (tau0 hω) ≤ goodGamma M' :=
    le_goodGamma hS (by rw [hM9, hSc]) (Or.inl (tau_piece_sl hk hu))
  have hstab := goodGamma_lift_stable hk hu (Or.inr rfl) hM
  have h0 : tau0 hω ∈ goodGamma M' := hN (Subgroup.mem_zpowers _)
  have h1 : tau1 hω ∈ goodGamma M' := hstab _ h0
  have h2 : tau2 hω ∈ goodGamma M' := hstab _ h1
  have hall : ∀ a : k, a = 0 ∨ a = 1 ∨ a = (u : k) ∨ a = (u : k) * u := by
    intro a
    rcases LinearFieldFour.eq_zero_or_eq_one_or hk u.ne_zero (val_ne_one hu) a with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (by
        rw [h, LinearFieldFour.omega_mul_omega hk u.ne_zero (val_ne_one hu)])))
  have := eq_top_of_x01 (goodGamma M') hstab (x01_mem_of_tau hω hall (goodGamma M') h0 h1 h2)
  exact le_of_eq this.symm

end

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320
