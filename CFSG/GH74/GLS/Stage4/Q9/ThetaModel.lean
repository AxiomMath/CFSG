module

public import CFSG.GH74.GLS.Stage4.Q9.Tables
public import CFSG.GH74.GLS.Stage4.Q9.PermChar
public import CFSG.GH74.GLS.Stage4.Q9.ChatOrders

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open CFSG CFSG.TwoRankLowerBound.Helpers

section Abstract

variable {H : Type*} [Group H] [Fintype H]

theorem inducedFunction_apply_of_notMem (N : Subgroup H) [N.Normal] (f : N → ℂ) {x : H}
    (hx : x ∉ N) : inducedFunction N f x = 0 := by
  classical
  unfold inducedFunction
  rw [Finset.sum_eq_zero, mul_zero]
  intro g _
  refine dite_eq_right ?_
  intro hg
  apply hx
  have h := Subgroup.Normal.conj_mem inferInstance _ hg g
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [e] at h

theorem sum_ite_mem_const (N : Subgroup H) [DecidablePred (· ∈ N)] (c : ℂ) :
    ∑ g : H, (if g ∈ N then c else 0) = (Nat.card N : ℂ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem inducedFunction_apply_of_index_two (N : Subgroup H) [N.Normal] (hN : N.index = 2)
    (f : N → ℂ) (hf : ∀ n m : N, f (m * n * m⁻¹) = f n) {s : H} (hs : s ∉ N) {x : H}
    (hx : x ∈ N) :
    inducedFunction N f x =
      f ⟨x, hx⟩ + f ⟨s * x * s⁻¹, Subgroup.Normal.conj_mem inferInstance x hx s⟩ := by
  classical
  have hcard : (Nat.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  set F : H → ℂ := fun g => f ⟨g⁻¹ * x * g, Subgroup.Normal.conj_mem' inferInstance x hx g⟩
    with hF
  have hterm : ∀ g : H,
      (if h : g⁻¹ * x * g ∈ N then f ⟨g⁻¹ * x * g, h⟩ else 0) = F g := fun g =>
    dite_eq_left _
  have hinv : ∀ g : H, ∀ n ∈ N, F (g * n) = F g := by
    intro g n hn
    have h := hf ⟨g⁻¹ * x * g, Subgroup.Normal.conj_mem' inferInstance x hx g⟩ ⟨n⁻¹, N.inv_mem hn⟩
    simp only [hF]
    rw [← h]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]
  have hnot : s⁻¹ ∉ N := fun h => hs (by simpa using N.inv_mem h)
  unfold inducedFunction
  simp only [hterm]
  have hsplit : ∑ g : H, F g = ∑ g : H, (if g ∈ N then F g else 0) +
      ∑ g : H, (if g ∈ N then 0 else F g) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : g ∈ N <;> simp [hg]
  have h1 : ∑ g : H, (if g ∈ N then F g else 0) = ∑ g : H, (if g ∈ N then F 1 else 0) := by
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : g ∈ N
    · simp only [hg, ite_true]
      have := hinv 1 g hg
      rwa [one_mul] at this
    · simp [hg]
  have h2 : ∑ g : H, (if g ∈ N then 0 else F g) = ∑ g : H, (if g ∈ N then F s⁻¹ else 0) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft s⁻¹) (fun g => if g ∈ N then 0 else F g)]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hiff : s⁻¹ * g ∈ N ↔ g ∉ N := by
      rw [Subgroup.mul_mem_iff_of_index_two hN]
      simp [hnot]
    simp only [Equiv.coe_mulLeft]
    by_cases hg : g ∈ N
    · have : s⁻¹ * g ∈ N ↔ False := by simp [hiff, hg]
      simp only [this, ite_false, hg, ite_true]
      exact hinv _ g hg
    · have : s⁻¹ * g ∈ N := hiff.mpr hg
      simp [this, hg]
  rw [hsplit, h1, h2, sum_ite_mem_const, sum_ite_mem_const]
  have e1 : F 1 = f ⟨x, hx⟩ := by
    simp only [hF]
    congr 1
    apply Subtype.ext
    simp
  have e2 : F s⁻¹ = f ⟨s * x * s⁻¹, Subgroup.Normal.conj_mem inferInstance x hx s⟩ := by
    simp only [hF]
    congr 1
    apply Subtype.ext
    simp
  rw [e1, e2]
  field_simp

end Abstract

@[expose] def chatFst : ↥Chat →* Lg := (MonoidHom.fst Lg Lg).comp Chat.subtype

@[expose] def chatSnd : ↥Chat →* Lg := (MonoidHom.snd Lg Lg).comp Chat.subtype

@[simp] theorem chatFst_apply (c : ↥Chat) : chatFst c = c.1.1 := rfl

@[simp] theorem chatSnd_apply (c : ↥Chat) : chatSnd c = c.1.2 := rfl

@[expose] def chatParity : ↥Chat →* Multiplicative (ZMod 2) := parityL.comp chatFst

@[expose] def NHat : Subgroup ↥Chat := chatParity.ker

instance : NHat.Normal := inferInstanceAs (chatParity.ker).Normal

theorem parityL_snd_of_mem_NHat {c : ↥Chat} (hc : c ∈ NHat) : parityL c.1.2 = 1 :=
  (mem_Chat_iff.mp c.2).symm.trans hc

@[expose] def tauHatC : ↥Chat := ⟨tauHat, tauHat_mem⟩

theorem tauHatC_notMem_NHat : tauHatC ∉ NHat := parityL_tauL

theorem chatParity_surjective : Function.Surjective chatParity := by
  intro y
  have hy : y = 1 ∨ y = Multiplicative.ofAdd 1 := by revert y; decide
  rcases hy with rfl | rfl
  · exact ⟨1, map_one chatParity⟩
  · exact ⟨tauHatC, rfl⟩

theorem index_NHat : NHat.index = 2 := by
  rw [NHat, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ chatParity_surjective,
    Subgroup.card_top]
  simp

theorem left_mul_of_parityL_eq_one {a b : Lg} (ha : parityL a = 1) :
    (a * b).left = a.left * b.left := by
  rw [SemidirectProduct.mul_left]
  have h : a.right = 1 := ha
  rw [h, map_one]
  rfl

@[expose] def leftHomOfInner {G : Type*} [Group G] (π : G →* Lg)
    (hπ : ∀ g, parityL (π g) = 1) : G →* SL2 where
  toFun g := (π g).left
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; exact left_mul_of_parityL_eq_one (hπ a)

@[expose] def leftHom1 : ↥NHat →* SL2 :=
  leftHomOfInner (chatFst.comp NHat.subtype) fun n => n.2

@[expose] def leftHom2 : ↥NHat →* SL2 :=
  leftHomOfInner (chatSnd.comp NHat.subtype) fun n => parityL_snd_of_mem_NHat n.2

@[expose] noncomputable def alphaHat : ↥Chat → ℂ := fun c => aFn c.1.1 * aFn c.1.2

@[expose] noncomputable def rhoLamN : ↥NHat → ℂ := fun n =>
  rhoC (mkL (n : ↥Chat).1.1.left) * lamC (mkL (n : ↥Chat).1.2.left)

@[expose] noncomputable def betaHat : ↥Chat → ℂ := inducedFunction NHat rhoLamN

@[expose] noncomputable def thetaHat : ↥Chat → ℂ := 1 - alphaHat + betaHat

theorem thetaHat_apply_eq (c : ↥Chat) : thetaHat c = 1 - alphaHat c + betaHat c := rfl

theorem alphaHat_mem : alphaHat ∈ BlocksVChar ↥Chat :=
  blocksVChar_mul (blocksVChar_comp chatFst aFn_mem_blocksVChar)
    (blocksVChar_comp chatSnd aFn_mem_blocksVChar)

theorem rhoLamN_mem : rhoLamN ∈ BlocksVChar ↥NHat :=
  blocksVChar_mul (blocksVChar_comp (mkL.comp leftHom1) rhoC_mem)
    (blocksVChar_comp (mkL.comp leftHom2) lamC_mem)

theorem rhoLamN_conj (n m : ↥NHat) : rhoLamN (m * n * m⁻¹) = rhoLamN n :=
  blocksVChar_isClassFunction rhoLamN_mem n m

theorem betaHat_mem : betaHat ∈ BlocksVChar ↥Chat :=
  inducedFunction_mem_blocksVChar NHat rhoLamN_mem

theorem alphaHat_apply
    (c : ↥Chat) : alphaHat c = ((aTab c.1.1 * aTab c.1.2 : ℤ) : ℂ) := by
  show aFn c.1.1 * aFn c.1.2 = _
  rw [aFn_eq_aTab, aFn_eq_aTab]
  push_cast
  rfl

theorem betaHat_apply_outer (c : ↥Chat) (h : parityL c.1.1 ≠ 1) : betaHat c = 0 :=
  inducedFunction_apply_of_notMem NHat rhoLamN h

theorem tauL_conj_left_of_parityL_eq_one {l : Lg} (hl : parityL l = 1) :
    (tauL * l * tauL⁻¹).left = sigmaAut l.left := by
  obtain ⟨g, rfl⟩ := exists_innerL_of_parityL_eq_one hl
  rw [tauL_conj_innerL]
  rfl

theorem betaHat_apply_inner
    (l₁ l₂ : Lg) (h : parityL l₁ = parityL l₂) (h₁ : parityL l₁ = 1) :
    betaHat ⟨(l₁, l₂), mem_Chat_iff.mpr h⟩ =
      rhoTab (repIdx l₁.left) * (muTab (repIdx l₂.left) : ℂ) := by
  have h₂ : parityL l₂ = 1 := h.symm.trans h₁
  have hc : (⟨(l₁, l₂), mem_Chat_iff.mpr h⟩ : ↥Chat) ∈ NHat := h₁
  have key := inducedFunction_apply_of_index_two NHat index_NHat rhoLamN rhoLamN_conj
    tauHatC_notMem_NHat hc
  show inducedFunction NHat rhoLamN _ = _
  rw [key]
  show rhoC (mkL l₁.left) * lamC (mkL l₂.left) +
    rhoC (mkL (tauL * l₁ * tauL⁻¹).left) * lamC (mkL (tauL * l₂ * tauL⁻¹).left) = _
  rw [tauL_conj_left_of_parityL_eq_one h₁, tauL_conj_left_of_parityL_eq_one h₂, rhoC_sigma,
    ← mul_add, lam_sum_sigma, rhoC_eq_rhoTab]

theorem betaHat_apply (l₁ l₂ : Lg) (h : parityL l₁ = parityL l₂) :
    betaHat ⟨(l₁, l₂), mem_Chat_iff.mpr h⟩ =
      if parityL l₁ = 1 then rhoTab (repIdx l₁.left) * (muTab (repIdx l₂.left) : ℂ) else 0 := by
  by_cases h₁ : parityL l₁ = 1
  · rw [betaHat_apply_inner l₁ l₂ h h₁, ite_eq_left h₁]
  · rw [betaHat_apply_outer ⟨(l₁, l₂), mem_Chat_iff.mpr h⟩ h₁, ite_eq_right h₁]

theorem alphaHat_conj
    (c : ↥Chat) : starRingEnd ℂ (alphaHat c) = alphaHat c := by
  rw [alphaHat_apply, map_intCast]

theorem betaHat_conj
    (c : ↥Chat) : starRingEnd ℂ (betaHat c) = betaHat c := by
  obtain ⟨⟨l₁, l₂⟩, hc⟩ := c
  rw [betaHat_apply l₁ l₂ (mem_Chat_iff.mp hc)]
  by_cases h₁ : parityL l₁ = 1
  · rw [ite_eq_left h₁, map_mul, rhoTab_conj, map_intCast]
  · rw [ite_eq_right h₁, map_zero]

theorem innerL_minusOne_mem_BL : innerL minusOne ∈ BL := by
  rw [innerL_apply, mk_one_mem_BL_iff]
  decide

theorem aTab_mul_innerL_minusOne (l : Lg) : aTab (l * innerL minusOne) = aTab l := by
  have hiff : ∀ x : Lg, x⁻¹ * (l * innerL minusOne) * x ∈ BL ↔ x⁻¹ * l * x ∈ BL := by
    intro x
    have hc : innerL minusOne * x = x * innerL minusOne := (innerL_minusOne_comm x).symm
    have e : x⁻¹ * (l * innerL minusOne) * x = (x⁻¹ * l * x) * innerL minusOne :=
      calc x⁻¹ * (l * innerL minusOne) * x = x⁻¹ * l * (innerL minusOne * x) := by
            simp only [mul_assoc]
        _ = x⁻¹ * l * (x * innerL minusOne) := by rw [hc]
        _ = (x⁻¹ * l * x) * innerL minusOne := by simp only [mul_assoc]
    rw [e]
    exact Subgroup.mul_mem_cancel_right BL innerL_minusOne_mem_BL
  unfold aTab
  simp only [hiff]

theorem aFn_mul_innerL_minusOne
    (l : Lg) : aFn (l * innerL minusOne) = aFn l := by
  rw [aFn_eq_aTab, aFn_eq_aTab, aTab_mul_innerL_minusOne]

theorem parityL_mul_innerL_minusOne (l : Lg) : parityL (l * innerL minusOne) = parityL l := by
  rw [map_mul, parityL_innerL, mul_one]

theorem left_mul_innerL_minusOne (l : Lg) : (l * innerL minusOne).left = l.left * minusOne := by
  rw [SemidirectProduct.mul_left]
  show l.left * sigmaHom l.right minusOne = _
  rw [sigmaHom_minusOne]

theorem alphaHat_mul_kappa (c : ↥Chat) :
    alphaHat (c * ⟨kappa0, kappa0_mem⟩) = alphaHat c := by
  show aFn (c.1.1 * innerL minusOne) * aFn (c.1.2 * innerL minusOne) = aFn c.1.1 * aFn c.1.2
  rw [aFn_mul_innerL_minusOne, aFn_mul_innerL_minusOne]

theorem betaHat_mul_kappa (c : ↥Chat) :
    betaHat (c * ⟨kappa0, kappa0_mem⟩) = betaHat c := by
  obtain ⟨⟨l₁, l₂⟩, hc⟩ := c
  have hp : parityL l₁ = parityL l₂ := mem_Chat_iff.mp hc
  have hp' : parityL (l₁ * innerL minusOne) = parityL (l₂ * innerL minusOne) := by
    rw [parityL_mul_innerL_minusOne, parityL_mul_innerL_minusOne]; exact hp
  show betaHat ⟨(l₁ * innerL minusOne, l₂ * innerL minusOne), mem_Chat_iff.mpr hp'⟩ =
    betaHat ⟨(l₁, l₂), hc⟩
  by_cases h₁ : parityL l₁ = 1
  · rw [betaHat_apply_inner _ _ hp' (by rw [parityL_mul_innerL_minusOne]; exact h₁),
      betaHat_apply_inner l₁ l₂ hp h₁, left_mul_innerL_minusOne, left_mul_innerL_minusOne,
      repIdx_neg_mul, repIdx_neg_mul]
  · rw [betaHat_apply_outer ⟨(l₁ * innerL minusOne, l₂ * innerL minusOne), mem_Chat_iff.mpr hp'⟩
      (by show parityL (l₁ * innerL minusOne) ≠ 1; rwa [parityL_mul_innerL_minusOne]),
      betaHat_apply_outer ⟨(l₁, l₂), hc⟩ h₁]

theorem alphaHat_mul_kappaC
    (c : ↥Chat) : alphaHat (c * kappaC) = alphaHat c :=
  alphaHat_mul_kappa c

theorem betaHat_mul_kappaC
    (c : ↥Chat) : betaHat (c * kappaC) = betaHat c :=
  betaHat_mul_kappa c

theorem alphaHat_eq_of_mkC_eq
    {a b : ↥Chat} (h : mkC a = mkC b) : alphaHat a = alphaHat b := by
  rcases mkC_eq_mkC_iff.mp h with rfl | rfl
  · rfl
  · exact (alphaHat_mul_kappaC a).symm

theorem betaHat_eq_of_mkC_eq
    {a b : ↥Chat} (h : mkC a = mkC b) : betaHat a = betaHat b := by
  rcases mkC_eq_mkC_iff.mp h with rfl | rfl
  · rfl
  · exact (betaHat_mul_kappaC a).symm

theorem alphaHat_one : alphaHat 1 = 81 := by
  have h : aTab (1 : Lg) = 9 := (aTab_eq_nine_iff 1).mpr (Or.inl rfl)
  rw [alphaHat_apply]
  show (((aTab 1 * aTab 1 : ℤ)) : ℂ) = 81
  rw [h]
  norm_num

theorem betaHat_one : betaHat 1 = 80 := by
  have h := betaHat_apply_inner 1 1 rfl (map_one parityL)
  have e : (1 : ↥Chat) = ⟨((1 : Lg), (1 : Lg)), mem_Chat_iff.mpr rfl⟩ := rfl
  have hr : repIdx ((1 : Lg).left) = 0 := repIdx_repList 0
  rw [e, h, hr]
  show (8 : ℂ) * ((10 : ℤ) : ℂ) = 80
  norm_num

theorem alphaHat_inl1_minusOne : alphaHat (inl1 minusOne) = 81 := by
  have h9 : aTab (innerL minusOne) = 9 := (aTab_eq_nine_iff _).mpr (Or.inr rfl)
  have h1 : aTab (1 : Lg) = 9 := (aTab_eq_nine_iff 1).mpr (Or.inl rfl)
  rw [alphaHat_apply]
  show (((aTab (innerL minusOne) * aTab 1 : ℤ)) : ℂ) = 81
  rw [h9, h1]
  norm_num

theorem betaHat_inl1_minusOne : betaHat (inl1 minusOne) = 80 := by
  have hp : parityL (innerL minusOne) = parityL (1 : Lg) := by rw [parityL_innerL, map_one]
  have h := betaHat_apply_inner (innerL minusOne) 1 hp (parityL_innerL minusOne)
  have e : inl1 minusOne = ⟨(innerL minusOne, (1 : Lg)), mem_Chat_iff.mpr hp⟩ := rfl
  have hr : repIdx ((innerL minusOne).left) = 0 := (repIdx_eq_zero_iff _).mpr (Or.inr rfl)
  have hr1 : repIdx ((1 : Lg).left) = 0 := repIdx_repList 0
  rw [e, h, hr, hr1]
  show (8 : ℂ) * ((10 : ℤ) : ℂ) = 80
  norm_num

theorem thetaHat_inl1_minusOne
    : thetaHat (inl1 minusOne) = 0 := by
  rw [thetaHat_apply_eq, alphaHat_inl1_minusOne, betaHat_inl1_minusOne]
  norm_num

end CFSG.GH74.GLS.Stage4.Q9
