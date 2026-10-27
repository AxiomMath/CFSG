module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Dickson

public section

namespace CFSG.QuasithinUnique.A5.G3

open Matrix MatrixGroups Equiv

variable {F : Type*} [Field F]

@[expose] def uT (t : F) : SL(2, F) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem uT_coe (t : F) : ((uT t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

theorem uT_zero : uT (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uT]

theorem uT_add (s t : F) : uT s * uT t = uT (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, uT_coe, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uT_injective : Function.Injective (uT : F → SL(2, F)) := by
  intro s t h
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [uT_coe] using this

@[expose] def uHom : Multiplicative F →* SL(2, F) where
  toFun t := uT (Multiplicative.toAdd t)
  map_one' := by simp [uT_zero]
  map_mul' s t := by simp [uT_add]

@[expose] def Ugrp (F : Type*) [Field F] : Subgroup SL(2, F) := (uHom (F := F)).range

theorem mem_Ugrp {g : SL(2, F)} : g ∈ Ugrp F ↔ ∃ t : F, g = uT t := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.toAdd t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, rfl⟩

theorem uHom_injective : Function.Injective (uHom (F := F)) := by
  intro s t h
  exact Multiplicative.toAdd.injective (uT_injective (F := F) h)

theorem lowerLeft_of_mem_Ugrp {g : SL(2, F)} (h : g ∈ Ugrp F) : g 1 0 = 0 := by
  obtain ⟨t, rfl⟩ := mem_Ugrp.mp h
  simp [uT_coe]

theorem conj_uT_10 (g : SL(2, F)) (t : F) :
    ((g * uT t * g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = -(g 1 0) ^ 2 * t := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, uT_coe, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem lowerLeft_zero_of_conj_mem {g : SL(2, F)} {t : F} (ht : t ≠ 0)
    (h : g * uT t * g⁻¹ ∈ Ugrp F) : g 1 0 = 0 := by
  have h1 := lowerLeft_of_mem_Ugrp h
  have h2 : -(g 1 0) ^ 2 * t = 0 := by rw [← conj_uT_10]; exact h1
  have h3 : (g 1 0) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · simpa using h
    · exact absurd h ht
  exact (pow_eq_zero_iff two_ne_zero).mp h3

theorem mem_Ugrp_of_commute [CharP F 2] {g : SL(2, F)} {t : F} (ht : t ≠ 0)
    (h : g * uT t = uT t * g) : g ∈ Ugrp F := by
  have e00 := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have e01 := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [Matrix.SpecialLinearGroup.coe_mul, uT_coe, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have hd := g.det_coe
  rw [Matrix.det_fin_two] at hd
  have hc : g 1 0 = 0 := by
    rcases e00 with h | h
    · exact absurd h ht
    · exact h
  have had : g 0 0 = g 1 1 := by
    have h1 : t * (g 0 0 - g 1 1) = 0 := by linear_combination e01
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h ht
    · exact sub_eq_zero.mp h
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have ha : g 0 0 = 1 := by
    have h3 : (g 0 0 - 1) ^ 2 = 0 := by
      rw [hc, ← had] at hd
      linear_combination hd + (1 - g 0 0) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
  refine mem_Ugrp.mpr ⟨g 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uT_coe, ha, hc, ← had]

@[expose] def Bgrp (F : Type*) [Field F] : Subgroup SL(2, F) where
  carrier := {g | g 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    have hg' : g 1 0 = 0 := hg
    have hh' : h 1 0 = 0 := hh
    show (g * h) 1 0 = 0
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg', hh']
  inv_mem' := by
    intro g hg
    have hg' : g 1 0 = 0 := hg
    show (g⁻¹) 1 0 = 0
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hg']

theorem mem_Bgrp {g : SL(2, F)} : g ∈ Bgrp F ↔ g 1 0 = 0 := Iff.rfl

theorem Bgrp_det (g : Bgrp F) : (g.1 : SL(2, F)) 0 0 * (g.1 : SL(2, F)) 1 1 = 1 := by
  have hd := g.1.det_coe
  rw [Matrix.det_fin_two] at hd
  have h10 : (g.1 : SL(2, F)) 1 0 = 0 := g.2
  simpa [h10] using hd

@[expose] def dHom : Bgrp F →* Fˣ where
  toFun g := Units.mk0 ((g.1 : SL(2, F)) 0 0) (left_ne_zero_of_mul_eq_one (Bgrp_det g))
  map_one' := by ext; simp
  map_mul' g h := by
    ext
    have h10 : (h.1 : SL(2, F)) 1 0 = 0 := h.2
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h10]

theorem uT_mem_Bgrp (t : F) : uT t ∈ Bgrp F := by
  simp [mem_Bgrp, uT_coe]

theorem Bgrp_solvable : Group.IsSolvable (Bgrp F) := by
  let f : Multiplicative F →* Bgrp F :=
    { toFun := fun t => ⟨uT (Multiplicative.toAdd t), uT_mem_Bgrp _⟩
      map_one' := by ext1; simp [uT_zero]
      map_mul' := fun s t => by ext1; simp [uT_add] }
  have hfg : (dHom (F := F)).ker ≤ f.range := by
    intro g hg
    have h1 : (g.1 : SL(2, F)) 0 0 = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hg)
      simpa [dHom] using this
    have h10 : (g.1 : SL(2, F)) 1 0 = 0 := g.2
    have h11 : (g.1 : SL(2, F)) 1 1 = 1 := by
      have := Bgrp_det g
      rwa [h1, one_mul] at this
    refine ⟨Multiplicative.ofAdd ((g.1 : SL(2, F)) 0 1), ?_⟩
    ext1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [f, uT_coe, h1, h10, h11]
  have h1 : Group.IsSolvable (Multiplicative F) := inferInstance
  have h2 : Group.IsSolvable Fˣ := inferInstance
  exact Group.isSolvable_of_ker_le_range f dHom hfg

theorem card_Ugrp [Finite F] : Nat.card (Ugrp F) = Nat.card F := by
  have h := Nat.card_congr (MonoidHom.ofInjective (uHom_injective (F := F))).toEquiv
  rw [← Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)]
  exact h.symm

theorem card_SL2 [Fintype F] :
    Nat.card SL(2, F) = Fintype.card F * (Fintype.card F ^ 2 - 1) :=
  CFSG.QuasithinUnique.Lin2.card_specialLinear_two

theorem isPGroup_Ugrp [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) : IsPGroup 2 (Ugrp F) :=
  IsPGroup.of_card ((card_Ugrp).trans hF)

theorem index_Ugrp_odd [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ¬ 2 ∣ (Ugrp F).index := by
  have : Fintype F := Fintype.ofFinite F
  have h1 := Subgroup.card_mul_index (Ugrp F)
  rw [card_Ugrp, card_SL2, ← Nat.card_eq_fintype_card] at h1
  rw [hF] at h1
  have hpos : 0 < 2 ^ n := by positivity
  have h2 : (Ugrp F).index = (2 ^ n) ^ 2 - 1 := by
    have : 2 ^ n * (Ugrp F).index = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [h1]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  rw [h2]
  have h3 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
  have h4 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ hpos
  omega

theorem exists_conj_Ugrp [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    {V : Subgroup SL(2, F)} (hV : IsPGroup 2 V) (hV' : ¬ 2 ∣ V.index) :
    ∃ g : SL(2, F), ∀ x, x ∈ V ↔ g⁻¹ * x * g ∈ Ugrp F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U : Sylow 2 SL(2, F) := (isPGroup_Ugrp hF).toSylow (index_Ugrp_odd hn hF)
  let W : Sylow 2 SL(2, F) := hV.toSylow hV'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, F) U W
  refine ⟨g, fun x => ?_⟩
  have h1 : (W : Subgroup SL(2, F)) = V := rfl
  have h2 : (U : Subgroup SL(2, F)) = Ugrp F := rfl
  rw [← h1, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← h2]
  simp [MulAut.smul_def, mul_assoc]

theorem charP_two_of_card [Finite F] {n : ℕ} (h : Nat.card F = 2 ^ n) : CharP F 2 := by
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : Nat.Prime p := CharP.char_is_prime F p
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨k, -, hq⟩ := FiniteField.card F p
  have h1 : p ∣ 2 ^ n := by
    rw [← h, hq]
    exact dvd_pow_self p k.ne_zero
  have h2 : p ∣ 2 := hpp.dvd_of_dvd_pow h1
  have h3 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2
  subst h3
  exact hp

theorem mul_self_eq_one_of_conj [CharP F 2] {g x : SL(2, F)} (hx : g⁻¹ * x * g ∈ Ugrp F) :
    x * x = 1 := by
  obtain ⟨t, ht⟩ := mem_Ugrp.mp hx
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have htt : t + t = 0 := by linear_combination t * h2
  have h1 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
    rw [ht, uT_add, htt, uT_zero]
  calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem card_of_conj [Finite F] {V : Subgroup SL(2, F)} {g : SL(2, F)}
    (hg : ∀ x, x ∈ V ↔ g⁻¹ * x * g ∈ Ugrp F) : Nat.card V = Nat.card F := by
  rw [← card_Ugrp (F := F)]
  refine Nat.card_congr
    { toFun := fun v => ⟨g⁻¹ * v.1 * g, (hg v.1).mp v.2⟩
      invFun := fun u => ⟨g * u.1 * g⁻¹, (hg _).mpr (by simp [mul_assoc])⟩
      left_inv := fun v => by ext; simp [mul_assoc]
      right_inv := fun u => by ext; simp [mul_assoc] }

theorem mem_of_commute_of_mem [CharP F 2] {V : Subgroup SL(2, F)} {g : SL(2, F)}
    (hg : ∀ x, x ∈ V ↔ g⁻¹ * x * g ∈ Ugrp F) {p y : SL(2, F)} (hp : p ∈ V) (hp1 : p ≠ 1)
    (hy : y * p = p * y) : y ∈ V := by
  obtain ⟨t, ht⟩ := mem_Ugrp.mp ((hg p).mp hp)
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hp1
    rw [uT_zero] at ht
    calc p = g * (g⁻¹ * p * g) * g⁻¹ := by group
      _ = 1 := by rw [ht]; group
  refine (hg y).mpr (mem_Ugrp_of_commute ht0 ?_)
  rw [← ht]
  calc g⁻¹ * y * g * (g⁻¹ * p * g) = g⁻¹ * (y * p) * g := by group
    _ = g⁻¹ * (p * y) * g := by rw [hy]
    _ = g⁻¹ * p * g * (g⁻¹ * y * g) := by group

theorem solvable_of_le_normalizer [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    {X Y : Subgroup SL(2, F)} (hX : IsPGroup 2 X) (hX1 : X ≠ ⊥)
    (hYX : Y ≤ Subgroup.normalizer (X : Set SL(2, F))) : Group.IsSolvable Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ :=
    exists_conj_Ugrp hn hF (V := (Q : Subgroup SL(2, F))) Q.isPGroup' Q.not_dvd_index
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hX1
  have hxX : (x : SL(2, F)) ∈ X := x.2
  have hxQ : (x : SL(2, F)) ∈ (Q : Subgroup SL(2, F)) := hXQ hxX
  obtain ⟨t, ht⟩ := mem_Ugrp.mp ((hg x).mp hxQ)
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hx1
    rw [uT_zero] at ht
    refine Subtype.ext ?_
    calc (x : SL(2, F)) = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have hB : ∀ y ∈ Y, g⁻¹ * y * g ∈ Bgrp F := by
    intro y hy
    have hyN := hYX hy
    have hyx : y * x * y⁻¹ ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp hyN x).mp hxX
      exact this
    have h1 : g⁻¹ * (y * x * y⁻¹) * g ∈ Ugrp F := (hg _).mp (hXQ hyx)
    have h2 : (g⁻¹ * y * g) * uT t * (g⁻¹ * y * g)⁻¹ ∈ Ugrp F := by
      have : (g⁻¹ * y * g) * uT t * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * x * y⁻¹) * g := by
        rw [← ht]; group
      rw [this]
      exact h1
    exact lowerLeft_zero_of_conj_mem ht0 h2
  let f : Y →* Bgrp F :=
    (((MulAut.conj g⁻¹).toMonoidHom.comp Y.subtype).codRestrict (Bgrp F)
      (fun y => by simpa [MulAut.conj_apply] using hB y.1 y.2))
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg (fun z : Bgrp F => (z : SL(2, F))) hab
    simp [f] at this
    exact this
  have : Group.IsSolvable (Bgrp F) := Bgrp_solvable
  exact Group.isSolvable_of_isSolvable_injective hf

theorem not_solvable_alt5 : ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
  intro h
  have hs : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 5))).mpr h
  have h2 := congrArg Subtype.val (hc Delta5.a0' Delta5.b0')
  revert h2
  show ¬ (Delta5.a0 * Delta5.b0 = Delta5.b0 * Delta5.a0)
  decide +kernel

@[expose] def invs5 : Finset (Perm (Fin 5)) := Finset.univ.filter fun a => a * a = 1 ∧ a ≠ 1

theorem mem_invs5 (a : Perm (Fin 5)) : a ∈ invs5 ↔ a * a = 1 ∧ a ≠ 1 := by
  simp [invs5]

theorem three_involutions_dependent : ∀ a ∈ invs5, ∀ b ∈ invs5, a * b = b * a → b ≠ a →
    ∀ c ∈ invs5, a * c = c * a → b * c = c * b → c ≠ a → c ≠ b → c ≠ a * b → False := by
  decide +kernel

theorem card_le_four_of_faithful {E : Type*} [Group E] [Finite E] (hE : ∀ x : E, x * x = 1)
    (ψ : E →* MulAut (alternatingGroup (Fin 5))) (hψ : Function.Injective ψ) :
    Nat.card E ≤ 4 := by
  classical
  have hex : ∀ e : E, ∃ σ : Perm (Fin 5), ∀ a : alternatingGroup (Fin 5),
      ((ψ e a : alternatingGroup (Fin 5)) : Perm (Fin 5)) = σ * a * σ⁻¹ :=
    fun e => Delta5.aut_inner (ψ e)
  choose s hs using hex
  have huniq : ∀ (e : E) (τ : Perm (Fin 5)), (∀ a : alternatingGroup (Fin 5),
      ((ψ e a : alternatingGroup (Fin 5)) : Perm (Fin 5)) = τ * a * τ⁻¹) → τ = s e := by
    intro e τ hτ
    have h1 : (s e)⁻¹ * τ = 1 := by
      apply Delta5.cent_alt
      intro a ha
      have h2 := (hs e ⟨a, Equiv.Perm.mem_alternatingGroup.mpr ha⟩).symm.trans
        (hτ ⟨a, Equiv.Perm.mem_alternatingGroup.mpr ha⟩)
      have h3 := congrArg (fun z => (s e)⁻¹ * z * τ) h2
      simp only [] at h3
      calc (s e)⁻¹ * τ * a = (s e)⁻¹ * (τ * a * τ⁻¹) * τ := by group
        _ = (s e)⁻¹ * (s e * a * (s e)⁻¹) * τ := by rw [← h2]
        _ = a * ((s e)⁻¹ * τ) := by group
    have h4 : τ = s e * ((s e)⁻¹ * τ) := by group
    rw [h4, h1, mul_one]
  have hmul : ∀ e e' : E, s (e * e') = s e * s e' := by
    intro e e'
    symm
    apply huniq
    intro a
    have h1 : ψ (e * e') a = ψ e (ψ e' a) := by simp
    rw [h1, hs e (ψ e' a)]
    have h2 : (((ψ e' a : alternatingGroup (Fin 5))) : Perm (Fin 5)) = s e' * a * (s e')⁻¹ :=
      hs e' a
    rw [h2]
    group
  have hone : s 1 = 1 := by
    symm
    apply huniq
    intro a
    simp
  have hinj : Function.Injective s := by
    intro e e' h
    have h1 : s (e⁻¹ * e') = 1 := by
      rw [hmul, ← h]
      have : s (e⁻¹ * e) = 1 := by rw [inv_mul_cancel, hone]
      rwa [hmul] at this
    have h2 : ψ (e⁻¹ * e') = 1 := by
      refine MulEquiv.ext fun a => ?_
      have h5 := hs (e⁻¹ * e') a
      rw [h1] at h5
      refine Subtype.ext ?_
      simpa using h5
    have h3 : e⁻¹ * e' = 1 := hψ (by rw [h2, map_one])
    exact inv_mul_eq_one.mp h3
  have hcomm : ∀ x y : E, x * y = y * x := by
    intro x y
    calc x * y = (x * y)⁻¹ * ((x * y) * (x * y)) := by group
      _ = (x * y)⁻¹ := by rw [hE (x * y), mul_one]
      _ = y⁻¹ * x⁻¹ := by group
      _ = y * x := by
        have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hE x)
        have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hE y)
        rw [hx, hy]
  by_contra hlt
  push Not at hlt
  have : Fintype E := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card] at hlt
  obtain ⟨a, ha⟩ : ∃ a : E, a ≠ 1 := by
    by_contra h
    push Not at h
    have : Fintype.card E ≤ 1 := Fintype.card_le_one_iff.mpr (fun x y => by rw [h x, h y])
    omega
  obtain ⟨b, hb⟩ : ∃ b : E, b ∉ ({1, a} : Finset E) := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset E) ⊆ {1, a} := fun x _ => h x
    have h2 := Finset.card_le_card this
    have h3 : ({1, a} : Finset E).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ] at h2
    omega
  obtain ⟨c, hc⟩ : ∃ c : E, c ∉ ({1, a, b, a * b} : Finset E) := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset E) ⊆ {1, a, b, a * b} := fun x _ => h x
    have h2 := Finset.card_le_card this
    have h3 : ({1, a, b, a * b} : Finset E).card ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp
    rw [Finset.card_univ] at h2
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb hc
  have hsq : ∀ x : E, x ≠ 1 → s x ∈ invs5 := fun x hx =>
    (mem_invs5 _).mpr ⟨by rw [← hmul, hE x, hone], fun h => hx (hinj (h.trans hone.symm))⟩
  refine three_involutions_dependent (s a) (hsq a ha) (s b) (hsq b hb.1) ?_ ?_ (s c) (hsq c hc.1)
    ?_ ?_ ?_ ?_ ?_
  · rw [← hmul, ← hmul, hcomm a b]
  · exact fun h => hb.2 (hinj h)
  · rw [← hmul, ← hmul, hcomm a c]
  · rw [← hmul, ← hmul, hcomm b c]
  · exact fun h => hc.2.1 (hinj h)
  · exact fun h => hc.2.2.1 (hinj h)
  · exact fun h => hc.2.2.2 (hinj (by rw [hmul]; exact h))

theorem sl2_index_normalizer [Finite F] {n : ℕ} (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ n)
    {Y V : Subgroup SL(2, F)} (θ : ↥Y ≃* alternatingGroup (Fin 5))
    (hV : IsPGroup 2 V) (hV' : ¬ 2 ∣ V.index) :
    ¬ (V ⊓ Subgroup.normalizer (Y : Set SL(2, F))).relIndex V ∣ 2 := by
  have hchar : CharP F 2 := charP_two_of_card hF
  have : Fintype F := Fintype.ofFinite F
  have hYcard : Nat.card Y = 60 := by
    rw [Nat.card_congr θ.toEquiv, Delta5.a5_card]
  have hn4 : 4 ≤ n := by
    by_contra hlt
    have h3 : n = 3 := by omega
    subst h3
    have hdvd : Nat.card Y ∣ Nat.card SL(2, F) := Subgroup.card_subgroup_dvd_card Y
    rw [card_SL2, ← Nat.card_eq_fintype_card, hF, hYcard] at hdvd
    revert hdvd
    decide
  obtain ⟨g, hg⟩ := exists_conj_Ugrp (by omega) hF hV hV'
  set E : Subgroup SL(2, F) := V ⊓ Subgroup.normalizer (Y : Set SL(2, F)) with hEdef
  have hEV : E ≤ V := inf_le_left
  have hEN : E ≤ Subgroup.normalizer (Y : Set SL(2, F)) := inf_le_right
  let ψ : E →* MulAut (alternatingGroup (Fin 5)) :=
    (MulAut.congr θ).toMonoidHom.comp ((Y.normalizerMonoidHom).comp (Subgroup.inclusion hEN))
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : Y.normalizerMonoidHom (Subgroup.inclusion hEN e) = 1 := by
      have h2 : (MulAut.congr θ) (Y.normalizerMonoidHom (Subgroup.inclusion hEN e)) = 1 := he
      exact (MulAut.congr θ).injective (h2.trans (map_one _).symm)
    have h3 : Subgroup.inclusion hEN e ∈ Y.normalizerMonoidHom.ker := h1
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h3
    have h4 : (e : SL(2, F)) ∈ Subgroup.centralizer (Y : Set SL(2, F)) := h3
    by_contra hne
    have hne' : (e : SL(2, F)) ≠ 1 := fun h => hne (Subtype.ext h)
    have hYV : Y ≤ V := by
      intro y hy
      refine mem_of_commute_of_mem hg (hEV e.2) hne' ?_
      exact Subgroup.mem_centralizer_iff.mp h4 y hy
    have hY2 : IsPGroup 2 Y := hV.to_le hYV
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card Y = 2 ^ k := hY2.exists_card_eq
    rw [hYcard] at hk
    have h5 : (2 ^ k) % 3 ≠ 0 := by
      intro h
      have : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
      omega
    omega
  have hE2 : ∀ x : E, x * x = 1 := by
    intro x
    refine Subtype.ext ?_
    exact mul_self_eq_one_of_conj ((hg _).mp (hEV x.2))
  have hcard : Nat.card E ≤ 4 := card_le_four_of_faithful hE2 ψ hψ
  intro hidx
  have h1 := Subgroup.relIndex_mul_card E V
  rw [inf_eq_left.mpr hEV, card_of_conj hg, hF] at h1
  have h2 : E.relIndex V ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
  have h3 : 2 ^ n ≤ 8 := by
    rw [← h1]
    calc E.relIndex V * Nat.card E ≤ 2 * 4 := Nat.mul_le_mul h2 hcard
      _ = 8 := by norm_num
  have h4 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
  omega

end CFSG.QuasithinUnique.A5.G3
