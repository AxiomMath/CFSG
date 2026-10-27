module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import Mathlib.LinearAlgebra.Eigenspace.Pi

public section

namespace CFSG.LieType.TwoRank

open Matrix

section Involution

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

private lemma pow_succ_eq_pow_smul_self_of_mul_self_eq_smul_self
    (S : Module.End F V) {c : F} (hS : S * S = c • S) (k : ℕ) :
    S ^ (k + 1) = c ^ k • S := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc S ^ (k + 1 + 1) = S ^ (k + 1) * S := by rw [pow_succ]
      _ = (c ^ k • S) * S := by rw [ih]
      _ = c ^ k • (S * S) := by rw [smul_mul_assoc]
      _ = c ^ k • (c • S) := by rw [hS]
      _ = (c ^ k * c) • S := by rw [smul_smul]
      _ = c ^ (k + 1) • S := by rw [pow_succ]

private lemma apply_eq_zero_of_mem_maxGenEigenspace_zero
    (S : Module.End F V) {c : F} (hc : c ≠ 0) (hS : S * S = c • S)
    {v : V} (hv : v ∈ S.maxGenEigenspace 0) : S v = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (S ^ k) v = 0 := by
    simpa using (Module.End.mem_maxGenEigenspace S 0 v).mp hv
  cases k with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hk
    rw [hk, map_zero]
  | succ j =>
    rw [pow_succ_eq_pow_smul_self_of_mul_self_eq_smul_self S hS j] at hk
    have hkj : c ^ j • (S v) = 0 := by simpa using hk
    exact (smul_eq_zero.mp hkj).resolve_left (pow_ne_zero j hc)

private lemma maxGenEigenspace_le_eigenspace_of_mul_self_eq_one
    (h2 : (2 : F) ≠ 0) {T : Module.End F V} (hT : T * T = 1) {μ : F} (hμ : μ ^ 2 = 1) :
    T.maxGenEigenspace μ ≤ T.eigenspace μ := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff]
  have hμ' : μ * μ = 1 := by simpa [pow_two] using hμ
  have hμne : μ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hμ'
    exact zero_ne_one hμ'
  have hc : (-(2 * μ) : F) ≠ 0 := by
    have h2μ : (2 : F) * μ ≠ 0 := mul_ne_zero h2 hμne
    exact neg_ne_zero.mpr h2μ
  have hTT : ∀ w : V, T (T w) = w := by
    intro w
    have h := congrArg (fun A : Module.End F V => A w) hT
    simpa [Module.End.mul_apply] using h
  have hS : (T - μ • 1) * (T - μ • 1) = (-(2 * μ)) • (T - μ • 1) := by
    ext w
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul, smul_sub, smul_smul]
    rw [hTT w, hμ']
    have hscalar : (-(2 * μ) : F) * μ = -2 := by
      rw [neg_mul, mul_assoc, hμ', mul_one]
    rw [hscalar]
    module
  have hv' : v ∈ (T - μ • 1).maxGenEigenspace 0 := by
    rw [← Module.End.maxGenEigenspace_eq_maxGenEigenspace_zero T μ]
    exact hv
  have hzero : (T - μ • 1) v = 0 :=
    apply_eq_zero_of_mem_maxGenEigenspace_zero (T - μ • 1) hc hS hv'
  simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using hzero

private lemma sq_eq_one_of_maxGenEigenspace_ne_bot
    {T : Module.End F V} (hT : T * T = 1) {μ : F}
    (h : T.maxGenEigenspace μ ≠ ⊥) : μ ^ 2 = 1 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp h
  have hex : ∃ k : ℕ, ((T - μ • 1) ^ k) v = 0 :=
    (Module.End.mem_maxGenEigenspace T μ v).mp hv
  have hker_ex : ∃ w : V, w ≠ 0 ∧ (T - μ • 1) w = 0 := by
    suffices H : ∀ k : ℕ, ((T - μ • 1) ^ k) v = 0 →
        v = 0 ∨ ∃ w : V, w ≠ 0 ∧ (T - μ • 1) w = 0 by
      obtain ⟨k, hk⟩ := hex
      rcases H k hk with h0 | hw
      · exact absurd h0 hv0
      · exact hw
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      cases k with
      | zero => exact Or.inl (by simpa using hk)
      | succ k =>
        rw [pow_succ'] at hk
        simp only [Module.End.mul_apply] at hk
        by_cases hk' : ((T - μ • 1) ^ k) v = 0
        · exact ih k (Nat.lt_succ_self k) hk'
        · exact Or.inr ⟨((T - μ • 1) ^ k) v, hk', hk⟩
  obtain ⟨w, hw0, hSw⟩ := hker_ex
  have hTw : T w = μ • w := by
    simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using hSw
  have hTTw : T (T w) = w := by
    have h := congrArg (fun A : Module.End F V => A w) hT
    simpa [Module.End.mul_apply] using h
  have hcoef : μ * μ - 1 = 0 := by
    have hww : (μ * μ) • w = w := by
      calc (μ * μ) • w = μ • (μ • w) := (smul_smul μ μ w).symm
        _ = μ • T w := by rw [hTw]
        _ = T (μ • w) := (map_smul T μ w).symm
        _ = T (T w) := by rw [hTw]
        _ = w := hTTw
    have hzero : (μ * μ - 1) • w = 0 := by
      rw [sub_smul, one_smul, hww, sub_self]
    exact (smul_eq_zero.mp hzero).resolve_right hw0
  rw [pow_two]
  exact sub_eq_zero.mp hcoef

private lemma iSup_maxGenEigenspace_eq_top_of_mul_self_eq_one
    (h2 : (2 : F) ≠ 0) (T : Module.End F V) (hT : T * T = 1) :
    ⨆ μ : F, T.maxGenEigenspace μ = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hTT : T (T v) = v := by
    have h := congrArg (fun A : Module.End F V => A v) hT
    simpa [Module.End.mul_apply] using h
  have h1 : v + T v ∈ T.eigenspace 1 := by
    rw [Module.End.mem_eigenspace_iff]
    rw [map_add, hTT, one_smul]
    abel
  have h2' : v - T v ∈ T.eigenspace (-1) := by
    rw [Module.End.mem_eigenspace_iff]
    rw [map_sub, hTT, neg_one_smul]
    abel
  have hv : v = (2⁻¹ : F) • (v + T v) + (2⁻¹ : F) • (v - T v) := by
    have hsum : v + T v + (v - T v) = (2 : F) • v := by
      rw [two_smul]
      abel
    rw [← smul_add, hsum, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hv1 : (2⁻¹ : F) • (v + T v) ∈ ⨆ μ : F, T.maxGenEigenspace μ :=
    Submodule.smul_mem _ _
      (le_iSup (fun μ : F => T.maxGenEigenspace μ) 1
        (Module.End.eigenspace_le_maxGenEigenspace h1))
  have hv2 : (2⁻¹ : F) • (v - T v) ∈ ⨆ μ : F, T.maxGenEigenspace μ :=
    Submodule.smul_mem _ _
      (le_iSup (fun μ : F => T.maxGenEigenspace μ) (-1)
        (Module.End.eigenspace_le_maxGenEigenspace h2'))
  rw [hv]
  exact add_mem hv1 hv2

end Involution

theorem card_le_two_pow_of_isElementaryAbelian {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {n : Type*} [Fintype n] [DecidableEq n] (A : Subgroup (GL n F)) [IsElementaryAbelian 2 A] :
    Nat.card A ≤ 2 ^ Fintype.card n := by
  classical
  let f : A →* Module.End F (n → F) :=
    (Units.coeHom (Module.End F (n → F))).comp
      ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp A.subtype)
  have hcomm : Pairwise fun i j : A => Commute (f i) (f j) := by
    intro i j _
    show f i * f j = f j * f i
    rw [← map_mul, ← map_mul, mul_comm' i j]
  have hsq : ∀ a : A, f a * f a = 1 := by
    intro a
    have haa : a * a = 1 := by
      apply Subtype.ext
      have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) (a : GL n F) a.2
      simpa [pow_two] using h
    calc f a * f a = f (a * a) := (map_mul f a a).symm
      _ = f 1 := by rw [haa]
      _ = 1 := map_one f
  have hspan_a : ∀ a : A, ⨆ μ : F, (f a).maxGenEigenspace μ = ⊤ :=
    fun a => iSup_maxGenEigenspace_eq_top_of_mul_self_eq_one h2 (f a) (hsq a)
  let W : (A → F) → Submodule F (n → F) :=
    fun χ => ⨅ a : A, (f a).maxGenEigenspace (χ a)
  have hspan : ⨆ χ : A → F, W χ = ⊤ := by
    have h :=
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        (f := fun a : A => f a) hcomm hspan_a
    simpa [W] using h
  have hind : iSupIndep W := by
    have hmaps : ∀ i j : A, ∀ μ : F, Set.MapsTo (f i) ((f j).maxGenEigenspace μ)
        ((f j).maxGenEigenspace μ) := by
      intro i j μ
      have hc : Commute (f j) (f i) := by
        rcases eq_or_ne i j with rfl | hij
        · exact Commute.refl _
        · exact (hcomm hij).symm
      exact Module.End.mapsTo_maxGenEigenspace_of_comm hc μ
    have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
      (f := fun a : A => f a) hmaps
    simpa [W] using h
  let X := {χ : (A → F) // W χ ≠ ⊥}
  letI : Fintype X := hind.fintypeNeBotOfFiniteDimensional
  have hXcard : Fintype.card X ≤ Fintype.card n := by
    have h1 : Fintype.card X ≤ Module.finrank F (n → F) :=
      hind.subtype_ne_bot_le_finrank
    rwa [Module.finrank_fintype_fun_eq_card] at h1
  have hval_sq : ∀ (χ : A → F), W χ ≠ ⊥ → ∀ a : A, (χ a) ^ 2 = 1 := by
    intro χ hχnz a
    apply sq_eq_one_of_maxGenEigenspace_ne_bot (hsq a)
    intro hbot
    apply hχnz
    have hle : W χ ≤ (f a).maxGenEigenspace (χ a) := iInf_le _ a
    rw [hbot] at hle
    exact le_bot_iff.mp hle
  have hact : ∀ (χ : A → F), W χ ≠ ⊥ → ∀ (a : A) (v : n → F), v ∈ W χ →
      f a v = χ a • v := by
    intro χ hχnz a v hv
    have hle : W χ ≤ (f a).eigenspace (χ a) :=
      le_trans (iInf_le _ a)
        (maxGenEigenspace_le_eigenspace_of_mul_self_eq_one h2 (hsq a) (hval_sq χ hχnz a))
    have hv' : v ∈ (f a).eigenspace (χ a) := hle hv
    rwa [Module.End.mem_eigenspace_iff] at hv'
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hab' : ((Matrix.GeneralLinearGroup.toLin (a : GL n F) : _) :
        Module.End F (n → F)) =
        ((Matrix.GeneralLinearGroup.toLin (b : GL n F) : _) : Module.End F (n → F)) := hab
    have h1 : Matrix.GeneralLinearGroup.toLin (a : GL n F) =
        Matrix.GeneralLinearGroup.toLin (b : GL n F) := Units.ext hab'
    exact Subtype.ext ((Matrix.GeneralLinearGroup.toLin).injective h1)
  have hinj : Function.Injective (fun a : A => fun χ : X => decide (χ.1 a = 1)) := by
    intro a b hab
    have hfab : f a = f b := by
      have hker : ∀ χ : A → F, W χ ≤ LinearMap.ker (f a - f b) := by
        intro χ
        by_cases hχ : W χ = ⊥
        · rw [hχ]; exact bot_le
        · intro v hv
          rw [LinearMap.mem_ker]
          have hd := congrFun hab (⟨χ, hχ⟩ : X)
          have hval : χ a = χ b := by
            by_cases ha1 : χ a = 1
            · have hb1 : χ b = 1 := by
                have hbt : decide (χ b = 1) = true := by simpa [ha1] using hd.symm
                exact of_decide_eq_true hbt
              rw [ha1, hb1]
            · have hbne : χ b ≠ 1 := by
                intro hb1
                have hbf : decide (χ b = 1) = false := by simpa [ha1] using hd.symm
                exact (of_decide_eq_false hbf) hb1
              rcases sq_eq_one_iff.mp (hval_sq χ hχ a) with h1 | h1
              · exact absurd h1 ha1
              · rcases sq_eq_one_iff.mp (hval_sq χ hχ b) with h2 | h2
                · exact absurd h2 hbne
                · rw [h1, h2]
          have hva := hact χ hχ a v hv
          have hvb := hact χ hχ b v hv
          rw [hval] at hva
          simp [LinearMap.sub_apply, hva, hvb]
      have htop : (⊤ : Submodule F (n → F)) ≤ LinearMap.ker (f a - f b) := by
        rw [← hspan]
        exact iSup_le hker
      have hz : f a - f b = 0 := by
        apply LinearMap.ext
        intro v
        have hv : v ∈ LinearMap.ker (f a - f b) := htop Submodule.mem_top
        simpa [LinearMap.mem_ker] using hv
      exact sub_eq_zero.mp hz
    exact hf_inj hfab
  calc Nat.card A ≤ Nat.card (X → Bool) := Nat.card_le_card_of_injective _ hinj
    _ = 2 ^ Fintype.card X := by
      rw [Nat.card_fun]
      simp [Nat.card_eq_fintype_card]
    _ ≤ 2 ^ Fintype.card n := Nat.pow_le_pow_right (by norm_num) hXcard

theorem two_mul_card_le_two_pow_of_neg_one_not_mem {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {n : Type*} [Fintype n] [DecidableEq n] (A : Subgroup (GL n F)) [IsElementaryAbelian 2 A]
    (hA : (-1 : GL n F) ∉ A) : 2 * Nat.card A ≤ 2 ^ Fintype.card n := by
  classical
  let z : GL n F := -1
  let Z : Subgroup (GL n F) := Subgroup.zpowers z
  have hz2 : z ^ 2 = 1 := by
    change (-1 : GL n F) ^ 2 = 1
    apply Units.ext
    simp [pow_two, neg_mul_neg]
  have hzne : z ≠ 1 := by
    intro h
    exact hA (show z ∈ A from by rw [h]; exact A.one_mem)
  have hzorder : orderOf z = 2 := orderOf_eq_prime hz2 hzne
  have hZcard : Nat.card Z = 2 := by
    show Nat.card (Subgroup.zpowers z) = 2
    rw [Nat.card_zpowers, hzorder]
  have hdisj : Disjoint A Z := by
    have hAz : z ∉ A := hA
    rw [Subgroup.disjoint_def]
    intro x hxA hxZ
    change x ∈ Subgroup.zpowers z at hxZ
    have hzfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, hz2⟩
    rw [IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hzfin, hzorder] at hxZ
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hxZ
    rw [Finset.mem_range] at hk
    have hk1 : k ≤ 1 := Nat.lt_succ_iff.mp hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
    · exact hkx.symm
    · have hxz : x = z := by simpa using hkx.symm
      exact absurd (hxz ▸ hxA) hAz
  have hz_center : z ∈ Subgroup.center (GL n F) := by
    rw [Subgroup.mem_center_iff]
    intro a
    change a * (-1 : GL n F) = (-1 : GL n F) * a
    apply Units.ext
    simp [mul_neg, neg_mul]
  have hZcenter : Z ≤ Subgroup.center (GL n F) := by
    show Subgroup.zpowers z ≤ Subgroup.center (GL n F)
    rw [Subgroup.zpowers_le]
    exact hz_center
  haveI : Z.Normal := Subgroup.normal_of_le_center hZcenter
  have hZcA : Z ≤ Subgroup.centralizer (A : Set (GL n F)) :=
    hZcenter.trans (Subgroup.center_le_centralizer _)
  have hbij : Function.Bijective
      (fun x : A × Z => (⟨(x.1 : GL n F) * (x.2 : GL n F),
        Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(A ⊔ Z))) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      refine Subgroup.mul_injective_of_disjoint hdisj ?_
      simpa using congrArg Subtype.val hxy
    · intro b
      have hb : (b : GL n F) ∈ A ⊔ Z := b.2
      rw [Subgroup.mem_sup_of_normal_right] at hb
      obtain ⟨y, hy, w, hw, hyw⟩ := hb
      exact ⟨(⟨y, hy⟩, ⟨w, hw⟩), Subtype.ext hyw⟩
  have hB_card : Nat.card ↥(A ⊔ Z) = Nat.card A * Nat.card Z := by
    have hcard : Nat.card (A × Z) = Nat.card ↥(A ⊔ Z) :=
      Nat.card_congr (Equiv.ofBijective _ hbij)
    rw [← hcard, Nat.card_prod]
  letI : IsElementaryAbelian 2 Z := by
    change IsElementaryAbelian 2 (Subgroup.zpowers z)
    exact IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  have hB_elem : IsElementaryAbelian 2 ↥(A ⊔ Z) :=
    IsElementaryAbelian.sup_of_le_centralizer hZcA
  letI : IsElementaryAbelian 2 ↥(A ⊔ Z) := hB_elem
  have hle := card_le_two_pow_of_isElementaryAbelian h2 (A ⊔ Z)
  rw [hB_card, hZcard] at hle
  calc 2 * Nat.card A = Nat.card A * 2 := Nat.mul_comm 2 (Nat.card A)
    _ ≤ 2 ^ Fintype.card n := hle

end CFSG.LieType.TwoRank
