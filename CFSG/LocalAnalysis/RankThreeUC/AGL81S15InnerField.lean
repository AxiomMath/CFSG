module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerCount
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped MatrixGroups
open Matrix

namespace InnerField

open InnerCount

theorem card_fix_sq_of_stable {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [Finite V] (σ : K →+* K) (hσ : ∀ c, σ (σ c) = c) (hσne : ∃ c, σ c ≠ c)
    (s : V ≃+ V) (hs : ∀ (c : K) (x : V), s (c • x) = σ c • s x) (hss : ∀ x, s (s x) = x)
    (P : Submodule K V) (hP : ∀ x ∈ P, s x ∈ P) :
    Nat.card {x : V // x ∈ P ∧ s x = x} ^ 2 = Nat.card P := by
  let s' : P ≃+ P :=
    { toFun := fun x => ⟨s x, hP x x.2⟩
      invFun := fun x => ⟨s x, hP x x.2⟩
      left_inv := fun x => Subtype.ext (hss x)
      right_inv := fun x => Subtype.ext (hss x)
      map_add' := fun x y => Subtype.ext (map_add s x.1 y.1) }
  have h := card_fix_sq_of_semilinear_involution σ hσ hσne s'
    (fun c x => Subtype.ext (hs c x)) (fun x => Subtype.ext (hss x))
  have e : {x : V // x ∈ P ∧ s x = x} ≃ {x : P // s' x = x} :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
      invFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e]
  exact h

variable {F : Type} [Field F] {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y]
  {E : Y ≃+ (Fin 3 → F)} {A : Subgroup (Y ≃ₗ[ZMod 2] Y)}

theorem hat_mul (E : Y ≃+ (Fin 3 → F)) (a b : Y ≃ₗ[ZMod 2] Y) (v : Fin 3 → F) :
    hat E (a * b) v = hat E a (hat E b v) := by
  show E ((a * b) (E.symm v)) = E (a (E.symm (E (b (E.symm v)))))
  rw [AddEquiv.symm_apply_apply]
  rfl

theorem hat_comm {a b : Y ≃ₗ[ZMod 2] Y} (hab : a * b = b * a) (v : Fin 3 → F) :
    hat E a (hat E b v) = hat E b (hat E a v) := by
  rw [← hat_mul, ← hat_mul, hab]

theorem hat_eq_mulVec [CharP F 2] (hs : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1)
    (h : (muHom hs).ker) (v : Fin 3 → F) :
    hat E h.1.1 v = (toSL hs h2 h : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
  have := toSLFun_spec hs h2 h (E.symm v)
  rw [AddEquiv.apply_symm_apply] at this
  exact this

@[expose] noncomputable def fixLin [CharP F 2] (hs : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1) :
    Submodule F (Fin 3 → F) :=
  ⨅ h : (muHom hs).ker, LinearMap.ker (CFSG.RankThree.FFModules.subOne (toSL hs h2 h))

theorem mem_fixLin [CharP F 2] (hs : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1)
    (v : Fin 3 → F) : v ∈ fixLin hs h2 ↔ ∀ h : (muHom hs).ker, hat E h.1.1 v = v := by
  simp only [fixLin, Submodule.mem_iInf, LinearMap.mem_ker,
    CFSG.RankThree.FFModules.subOne_apply, sub_eq_zero, hat_eq_mulVec hs h2]

theorem card_fix_le_of_ne_bot [Fintype F] [CharP F 2] (hs : AllSemilin E A)
    (h2 : ∀ a ∈ A, a * a = 1) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (a₀ : A)
    (hnl : mu hs a₀ ≠ 1) (hH : (muHom hs).ker ≠ ⊥) :
    Nat.card {y : Y // ∀ a ∈ A, a y = y} ≤ Fintype.card F := by
  haveI : Finite Y := Finite.of_equiv (Fin 3 → F) E.symm.toEquiv
  have hC : fixLin hs h2 ≠ ⊤ := by
    obtain ⟨h, h1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hH
    have hg1 : toSL hs h2 h ≠ 1 := fun hh =>
      h1 (toSL_injective hs h2 (hh.trans (map_one (toSL hs h2)).symm))
    intro hcon
    have hk : LinearMap.ker (CFSG.RankThree.FFModules.subOne (toSL hs h2 h)) = ⊤ := by
      refine eq_top_iff.mpr ?_
      rw [← hcon]
      exact iInf_le (fun h : (muHom hs).ker =>
        LinearMap.ker (CFSG.RankThree.FFModules.subOne (toSL hs h2 h))) h
    exact hg1 ((CFSG.RankThree.FFModules.subOne_eq_zero_iff _).mp (LinearMap.ker_eq_top.mp hk))
  have hfr : Module.finrank F (fixLin hs h2) ≤ 2 := by
    have := Submodule.finrank_lt hC
    rw [CFSG.RankThree.FFModules.finrank_fin3] at this
    omega
  have hcard : Nat.card (fixLin hs h2) ≤ Fintype.card F ^ 2 := by
    rw [CFSG.RankThree.FFModules.card_submodule]
    exact Nat.pow_le_pow_right Fintype.card_pos hfr
  have hstab : ∀ v ∈ fixLin hs h2, hat E a₀.1 v ∈ fixLin hs h2 := by
    intro v hv
    rw [mem_fixLin] at hv ⊢
    intro h
    rw [hat_comm (hc h.1.1 h.1.2 a₀.1 a₀.2), hv h]
  have hdesc := card_fix_sq_of_stable (K := F) (V := Fin 3 → F) (mu hs a₀).toRingHom
    (mu_involutive hs h2 a₀) (exists_ne_of_ne_one _ hnl) (hat E a₀.1) (hat_smul hs a₀)
    (hat_hat (h2 a₀.1 a₀.2)) (fixLin hs h2) hstab
  have hinj : Nat.card {y : Y // ∀ a ∈ A, a y = y} ≤
      Nat.card {x : Fin 3 → F // x ∈ fixLin hs h2 ∧ hat E a₀.1 x = x} := by
    refine Nat.card_le_card_of_injective (fun y => ⟨E y.1, ?_, ?_⟩) ?_
    · rw [mem_fixLin]
      intro h
      show E (h.1.1 (E.symm (E y.1))) = E y.1
      rw [AddEquiv.symm_apply_apply, y.2 h.1.1 h.1.2]
    · show E (a₀.1 (E.symm (E y.1))) = E y.1
      rw [AddEquiv.symm_apply_apply, y.2 a₀.1 a₀.2]
    · intro y1 y2 hxy
      apply Subtype.ext
      exact E.injective (congrArg (Subtype.val : {x : Fin 3 → F // x ∈ fixLin hs h2 ∧
        hat E a₀.1 x = x} → Fin 3 → F) hxy)
  have hle : Nat.card {x : Fin 3 → F // x ∈ fixLin hs h2 ∧ hat E a₀.1 x = x} ≤ Fintype.card F := by
    have h4 : Nat.card {x : Fin 3 → F // x ∈ fixLin hs h2 ∧ hat E a₀.1 x = x} ^ 2 ≤
        Fintype.card F ^ 2 := hdesc.le.trans hcard
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h4
  exact hinj.trans hle

section Conj

variable {V : Type*} [AddCommGroup V] [Module F V] (σ : F ≃+* F) (s : V ≃+ V)
  (hsσ : ∀ (c : F) (x : V), s (c • x) = σ c • s x) (hσσ : ∀ c, σ (σ c) = c)

@[expose] def conj (f : Module.End F V) : Module.End F V where
  toFun v := s (f (s v))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by simp only [hsσ, map_smul, hσσ, RingHom.id_apply]

include hsσ hσσ

theorem conj_apply (f : Module.End F V) (v : V) : conj σ s hsσ hσσ f v = s (f (s v)) :=
  rfl

theorem conj_add (f g : Module.End F V) :
    conj σ s hsσ hσσ (f + g) = conj σ s hsσ hσσ f + conj σ s hsσ hσσ g :=
  LinearMap.ext fun v => by simp only [conj_apply, LinearMap.add_apply, map_add]

theorem conj_smul (c : F) (f : Module.End F V) :
    conj σ s hsσ hσσ (c • f) = σ c • conj σ s hsσ hσσ f :=
  LinearMap.ext fun v => by simp only [conj_apply, LinearMap.smul_apply, hsσ]

theorem conj_conj (hss : ∀ x, s (s x) = x) (f : Module.End F V) :
    conj σ s hsσ hσσ (conj σ s hsσ hσσ f) = f :=
  LinearMap.ext fun v => by simp only [conj_apply, hss]

theorem conj_zero : conj σ s hsσ hσσ (0 : Module.End F V) = 0 :=
  LinearMap.ext fun v => by simp only [conj_apply, LinearMap.zero_apply, map_zero]

@[expose] def conjEquiv (hss : ∀ x, s (s x) = x) : Module.End F V ≃+ Module.End F V where
  toFun := conj σ s hsσ hσσ
  invFun := conj σ s hsσ hσσ
  left_inv := conj_conj σ s hsσ hσσ hss
  right_inv := conj_conj σ s hsσ hσσ hss
  map_add' := conj_add σ s hsσ hσσ

end Conj

theorem subOne_injective : Function.Injective (CFSG.RankThree.FFModules.subOne (F := F)) := by
  intro g g' hgg'
  apply Subtype.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  have := LinearMap.congr_fun hgg' v
  rw [CFSG.RankThree.FFModules.subOne_apply, CFSG.RankThree.FFModules.subOne_apply] at this
  exact sub_left_injective this

@[expose] noncomputable def spanSub [CharP F 2] (hs : AllSemilin E A)
    (h2 : ∀ a ∈ A, a * a = 1) : Submodule F (Module.End F (Fin 3 → F)) :=
  Submodule.span F
    (Set.range fun h : (muHom hs).ker => CFSG.RankThree.FFModules.subOne (toSL hs h2 h))

theorem conj_subOne [CharP F 2] (hs : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1)
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (a₀ : A) (h : (muHom hs).ker) :
    conj (mu hs a₀) (hat E a₀.1) (hat_smul hs a₀) (mu_involutive hs h2 a₀)
      (CFSG.RankThree.FFModules.subOne (toSL hs h2 h)) =
      CFSG.RankThree.FFModules.subOne (toSL hs h2 h) := by
  refine LinearMap.ext fun v => ?_
  have h1 : ∀ w, hat E a₀.1 (hat E h.1.1 w) = hat E h.1.1 (hat E a₀.1 w) := fun w =>
    hat_comm (hc a₀.1 a₀.2 h.1.1 h.1.2) w
  have h3 := hat_hat (E := E) (h2 a₀.1 a₀.2)
  show hat E a₀.1 (CFSG.RankThree.FFModules.subOne (toSL hs h2 h) (hat E a₀.1 v)) =
    CFSG.RankThree.FFModules.subOne (toSL hs h2 h) v
  rw [CFSG.RankThree.FFModules.subOne_apply, CFSG.RankThree.FFModules.subOne_apply,
    ← hat_eq_mulVec hs h2 h, ← hat_eq_mulVec hs h2 h, map_sub, h1, h3]

theorem conj_mem_spanSub [CharP F 2] (hs : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1)
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (a₀ : A) {f : Module.End F (Fin 3 → F)}
    (hf : f ∈ spanSub hs h2) :
    conj (mu hs a₀) (hat E a₀.1) (hat_smul hs a₀) (mu_involutive hs h2 a₀) f ∈
      spanSub hs h2 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    rw [conj_subOne hs h2 hc a₀ h]
    exact Submodule.subset_span ⟨h, rfl⟩
  | zero =>
    rw [conj_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [conj_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [conj_smul]
    exact Submodule.smul_mem _ _ hx

@[expose] def kerSub (S : Submodule F (Fin 3 → F)) : Submodule F (Module.End F (Fin 3 → F)) where
  carrier := {f | (∀ v ∈ S, f v = 0) ∧ ∀ v, f v ∈ S}
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    exact ⟨fun v hv => by rw [LinearMap.add_apply, hf1 v hv, hg1 v hv, add_zero],
      fun v => S.add_mem (hf2 v) (hg2 v)⟩
  zero_mem' := ⟨fun v _ => rfl, fun v => S.zero_mem⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    exact ⟨fun v hv => by rw [LinearMap.smul_apply, hf1 v hv, smul_zero],
      fun v => S.smul_mem c (hf2 v)⟩

theorem mem_kerSub {S : Submodule F (Fin 3 → F)} {f : Module.End F (Fin 3 → F)} :
    f ∈ kerSub S ↔ (∀ v ∈ S, f v = 0) ∧ ∀ v, f v ∈ S :=
  Iff.rfl

theorem card_kerSub_le [Fintype F] (S : Submodule F (Fin 3 → F))
    (hS : Module.finrank F S = 1 ∨ Module.finrank F S = 2) :
    Nat.card (kerSub S) ≤ Fintype.card F ^ 2 := by
  have : Finite (((Fin 3 → F) ⧸ S) →ₗ[F] S) := Module.finite_of_finite F
  let Φ : kerSub S → (((Fin 3 → F) ⧸ S) →ₗ[F] S) := fun f =>
    S.liftQ (f.1.codRestrict S (mem_kerSub.mp f.2).2) (by
      rw [LinearMap.ker_codRestrict]
      exact fun v hv => LinearMap.mem_ker.mpr ((mem_kerSub.mp f.2).1 v hv))
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    have := congrArg (fun φ : ((Fin 3 → F) ⧸ S) →ₗ[F] S =>
      ((φ (Submodule.Quotient.mk v) : S) : Fin 3 → F)) hfg
    simpa only [Φ, Submodule.liftQ_apply, LinearMap.codRestrict_apply] using this
  have h1 := Nat.card_le_card_of_injective _ hΦ
  have h3 : Nat.card (((Fin 3 → F) ⧸ S) →ₗ[F] S) = Fintype.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card,
      Module.finrank_linearMap]
    have h4 := Submodule.finrank_quotient_add_finrank S
    rw [CFSG.RankThree.FFModules.finrank_fin3] at h4
    congr 1
    rcases hS with h | h <;> rw [h] at h4 ⊢ <;> omega
  omega

theorem card_ker_le_of_ne_bot [Fintype F] [CharP F 2] (hs : AllSemilin E A)
    (h2 : ∀ a ∈ A, a * a = 1) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (a₀ : A)
    (hnl : mu hs a₀ ≠ 1) (hH : (muHom hs).ker ≠ ⊥) :
    Nat.card (muHom hs).ker ≤ Fintype.card F := by
  haveI : Finite (Module.End F (Fin 3 → F)) := Module.finite_of_finite F
  have hB2 : ∀ b ∈ (toSL hs h2).range, b * b = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (Subtype.ext (h2 a.1.1 a.1.2))
    rw [this, map_one]
  have hBc : ∀ b ∈ (toSL hs h2).range, ∀ c ∈ (toSL hs h2).range, b * c = c * b := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    have : a * b = b * a := Subtype.ext (Subtype.ext (hc a.1.1 a.1.2 b.1.1 b.1.2))
    rw [this]
  have hB : (toSL hs h2).range ≠ ⊥ := by
    obtain ⟨h, h1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hH
    have hg1 : toSL hs h2 h ≠ 1 := fun hh =>
      h1 (toSL_injective hs h2 (hh.trans (map_one (toSL hs h2)).symm))
    exact (Subgroup.ne_bot_iff_exists_ne_one).mpr
      ⟨⟨toSL hs h2 h, h, rfl⟩, fun hh => hg1 (congrArg Subtype.val hh)⟩
  obtain ⟨S, hS, hle⟩ := CFSG.RankThree.FFModules.exists_le_transvectionGroup hB2 hBc hB
  have hN : spanSub hs h2 ≤ kerSub S := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    have hT := hle ⟨h, rfl⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · exact LinearMap.mem_ker.mp (CFSG.RankThree.FFModules.le_ker_subOne hT hv)
    · exact CFSG.RankThree.FFModules.range_subOne_le hT (LinearMap.mem_range_self _ v)
  have hcardN : Nat.card (spanSub hs h2) ≤ Fintype.card F ^ 2 :=
    (Nat.card_le_card_of_injective (Submodule.inclusion hN)
      (Submodule.inclusion_injective hN)).trans (card_kerSub_le S hS)
  have hss := hat_hat (E := E) (h2 a₀.1 a₀.2)
  have hdesc := card_fix_sq_of_stable (K := F) (V := Module.End F (Fin 3 → F))
    (mu hs a₀).toRingHom (mu_involutive hs h2 a₀) (exists_ne_of_ne_one _ hnl)
    (conjEquiv (mu hs a₀) (hat E a₀.1) (hat_smul hs a₀) (mu_involutive hs h2 a₀) hss)
    (fun c f => conj_smul (mu hs a₀) (hat E a₀.1) (hat_smul hs a₀) (mu_involutive hs h2 a₀) c f)
    (fun f => conj_conj (mu hs a₀) (hat E a₀.1) (hat_smul hs a₀) (mu_involutive hs h2 a₀) hss f)
    (spanSub hs h2) fun f hf => conj_mem_spanSub hs h2 hc a₀ hf
  have hinj : Nat.card (muHom hs).ker ≤ Nat.card {x : Module.End F (Fin 3 → F) //
      x ∈ spanSub hs h2 ∧ conjEquiv (mu hs a₀) (hat E a₀.1) (hat_smul hs a₀)
        (mu_involutive hs h2 a₀) hss x = x} := by
    refine Nat.card_le_card_of_injective (fun h => ⟨CFSG.RankThree.FFModules.subOne
      (toSL hs h2 h), Submodule.subset_span ⟨h, rfl⟩, conj_subOne hs h2 hc a₀ h⟩) ?_
    intro h1 h3 hh
    exact toSL_injective hs h2 (subOne_injective (congrArg Subtype.val hh))
  have h4 : Nat.card {x : Module.End F (Fin 3 → F) // x ∈ spanSub hs h2 ∧
      conjEquiv (mu hs a₀) (hat E a₀.1) (hat_smul hs a₀) (mu_involutive hs h2 a₀) hss x = x} ^ 2 ≤
      Fintype.card F ^ 2 := hdesc.le.trans hcardN
  exact hinj.trans ((Nat.pow_le_pow_iff_left (by norm_num)).mp h4)

end InnerField

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
  (hF : Fintype.card F = 2 ^ n) {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y]
  (E : Y ≃+ (Fin 3 → F)) (A : Subgroup (Y ≃ₗ[ZMod 2] Y))
  (h2 : ∀ a ∈ A, a * a = 1) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
  (hsemi : ∀ a ∈ A, ∃ μ : F ≃+* F, ∀ (c : F) (y : Y),
    E (a (E.symm (c • E y))) = μ c • E (a y))

include hn hF h2 hc hsemi

theorem card_mul_card_fix_lt
    (hnl : ∃ a ∈ A, ∃ (c : F) (y : Y), E (a (E.symm (c • E y))) ≠ c • E (a y)) :
    Nat.card A * Nat.card {y : Y // ∀ a ∈ A, a y = y} < Fintype.card F ^ 3 := by
  haveI : Finite Y := Finite.of_equiv (Fin 3 → F) E.symm.toEquiv
  obtain ⟨a₀, ha₀, c, y, hne⟩ := hnl
  have hq : 4 ≤ Fintype.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hnl' : InnerCount.mu hsemi ⟨a₀, ha₀⟩ ≠ 1 := by
    intro h
    exact hne ((InnerCount.mem_ker_muHom_iff hsemi ⟨a₀, ha₀⟩).mp
      (by rw [MonoidHom.mem_ker]; exact h) c y)
  have hA2 := InnerCount.card_le_two_mul_card_ker hsemi h2
  by_cases hH : (InnerCount.muHom hsemi).ker = ⊥
  · have hA : Nat.card A ≤ 2 := by
      rw [hH, Subgroup.card_bot] at hA2
      omega
    have hx := InnerCount.card_fix_sq_of_nonlinear hsemi h2 ⟨a₀, ha₀⟩ hnl'
    have hle : Nat.card {y : Y // ∀ a ∈ A, a y = y} ≤ Nat.card {y : Y // a₀ y = y} :=
      Nat.card_le_card_of_injective (fun y => ⟨y.1, y.2 a₀ ha₀⟩) fun x y hxy => by
        apply Subtype.ext
        exact congrArg (Subtype.val : {y : Y // a₀ y = y} → Y) hxy
    have h64 : 64 ≤ Fintype.card F ^ 3 :=
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ Fintype.card F ^ 3 := Nat.pow_le_pow_left hq 3
    have h2x : 2 * Nat.card {y : Y // a₀ y = y} < Fintype.card F ^ 3 := by
      by_contra hcon
      have hcon' := not_lt.mp hcon
      have h5 : Fintype.card F ^ 3 * Fintype.card F ^ 3 ≤ 4 * Fintype.card F ^ 3 :=
        calc Fintype.card F ^ 3 * Fintype.card F ^ 3
            ≤ (2 * Nat.card {y : Y // a₀ y = y}) * (2 * Nat.card {y : Y // a₀ y = y}) :=
              Nat.mul_le_mul hcon' hcon'
          _ = 4 * Nat.card {y : Y // a₀ y = y} ^ 2 := by ring
          _ = 4 * Fintype.card F ^ 3 := by rw [hx]
      have := Nat.le_of_mul_le_mul_right h5 (by omega)
      omega
    calc Nat.card A * Nat.card {y : Y // ∀ a ∈ A, a y = y}
        ≤ 2 * Nat.card {y : Y // a₀ y = y} := Nat.mul_le_mul hA hle
      _ < Fintype.card F ^ 3 := h2x
  · have hHq := InnerField.card_ker_le_of_ne_bot hsemi h2 hc ⟨a₀, ha₀⟩ hnl' hH
    have hFq := InnerField.card_fix_le_of_ne_bot hsemi h2 hc ⟨a₀, ha₀⟩ hnl' hH
    have hq2 : 0 < Fintype.card F ^ 2 := by positivity
    calc Nat.card A * Nat.card {y : Y // ∀ a ∈ A, a y = y}
        ≤ (2 * Nat.card (InnerCount.muHom hsemi).ker) * Nat.card {y : Y // ∀ a ∈ A, a y = y} :=
          Nat.mul_le_mul_right _ hA2
      _ ≤ (2 * Fintype.card F) * Fintype.card F :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hHq) hFq
      _ < Fintype.card F ^ 3 := by
          nlinarith [Nat.mul_le_mul_left (Fintype.card F ^ 2) hq]

end CFSG.LocalAnalysis.RankThreeUC.S15
