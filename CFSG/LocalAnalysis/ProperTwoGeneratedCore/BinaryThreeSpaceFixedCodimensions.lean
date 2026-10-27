module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceTraceZeroIrreducible
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFlagKernel
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

open Matrix Module

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section FixedSpaces

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def fixedVec (B : Subgroup (V ≃ₗ[ZMod 2] V)) : Submodule (ZMod 2) V where
  carrier := {v | ∀ b ∈ B, b v = v}
  add_mem' := fun {v w} hv hw b hb => by rw [map_add, hv b hb, hw b hb]
  zero_mem' := fun b _ => map_zero b
  smul_mem' := fun c v hv b hb => by rw [map_smul, hv b hb]

@[expose] def fixedDual (B : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Submodule (ZMod 2) (Module.Dual (ZMod 2) V) where
  carrier := {f | ∀ b ∈ B, b.symm.dualMap f = f}
  add_mem' := fun {f f'} hf hf' b hb => by rw [map_add, hf b hb, hf' b hb]
  zero_mem' := fun b _ => map_zero _
  smul_mem' := fun c f hf b hb => by rw [map_smul, hf b hb]

@[expose] def fixedTraceZeroEnd (B : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Submodule (ZMod 2) (Module.End (ZMod 2) V) where
  carrier := {X | X ∈ traceZeroEnd V ∧
    ∀ b ∈ B, (b : V →ₗ[ZMod 2] V) ∘ₗ X ∘ₗ (b.symm : V →ₗ[ZMod 2] V) = X}
  add_mem' := fun {X Y} hX hY => ⟨(traceZeroEnd V).add_mem hX.1 hY.1, fun b hb => by
    rw [LinearMap.add_comp, LinearMap.comp_add, hX.2 b hb, hY.2 b hb]⟩
  zero_mem' := ⟨(traceZeroEnd V).zero_mem, fun b _ => by
    rw [LinearMap.zero_comp, LinearMap.comp_zero]⟩
  smul_mem' := fun c X hX => ⟨(traceZeroEnd V).smul_mem c hX.1, fun b hb => by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hX.2 b hb]⟩

end FixedSpaces

namespace FixedCodim

@[expose] def fixCol (K : Subgroup (GL (Fin 3) (ZMod 2))) :
    Submodule (ZMod 2) (Fin 3 → ZMod 2) where
  carrier := {v | ∀ k ∈ K, (k : Mat3) *ᵥ v = v}
  add_mem' := fun {v w} hv hw k hk => by rw [mulVec_add, hv k hk, hw k hk]
  zero_mem' := fun k _ => mulVec_zero _
  smul_mem' := fun c v hv k hk => by rw [mulVec_smul, hv k hk]

@[expose] def fixRow (K : Subgroup (GL (Fin 3) (ZMod 2))) :
    Submodule (ZMod 2) (Fin 3 → ZMod 2) where
  carrier := {w | ∀ k ∈ K, w ᵥ* (k : Mat3) = w}
  add_mem' := fun {v w} hv hw k hk => by rw [add_vecMul, hv k hk, hw k hk]
  zero_mem' := fun k _ => zero_vecMul _
  smul_mem' := fun c w hw k hk => by rw [smul_vecMul, hw k hk]

@[expose] def fixTr (K : Subgroup (GL (Fin 3) (ZMod 2))) : Submodule (ZMod 2) Mat3 where
  carrier := {X | X ∈ traceZero ∧ ∀ k ∈ K, conjLin k X = X}
  add_mem' := fun {X Y} hX hY =>
    ⟨traceZero.add_mem hX.1 hY.1, fun k hk => by rw [map_add, hX.2 k hk, hY.2 k hk]⟩
  zero_mem' := ⟨traceZero.zero_mem, fun k _ => map_zero _⟩
  smul_mem' := fun c X hX =>
    ⟨traceZero.smul_mem c hX.1, fun k hk => by rw [map_smul, hX.2 k hk]⟩

@[expose] def tmul (s s' : ZMod 2 × ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 × ZMod 2 :=
  (s.1 + s'.1, s.2.1 + s'.2.1 + s.1 * s'.2.2, s.2.2 + s'.2.2)

abbrev tGL (s : ZMod 2 × ZMod 2 × ZMod 2) : GL (Fin 3) (ZMod 2) := unitriGL s.1 s.2.1 s.2.2

theorem tGL_mul (s s' : ZMod 2 × ZMod 2 × ZMod 2) : tGL s * tGL s' = tGL (tmul s s') :=
  Units.ext (unitri_mul _ _ _ _ _ _)

theorem tGL_zero : tGL (0, 0, 0) = 1 := Units.ext unitri_zero

theorem tGL_injective : Function.Injective tGL := fun _ _ h =>
  tripleEquiv.injective (Subtype.ext h)

theorem coe_tGL (s : ZMod 2 × ZMod 2 × ZMod 2) : (tGL s : Mat3) = unitri s.1 s.2.1 s.2.2 := rfl

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem core_cards : ∀ P : ZMod 2 × ZMod 2 × ZMod 2 → Bool,
    P (0, 0, 0) = true →
    (∀ s s', P s = true → P s' = true → P (tmul s s') = true) →
    (∀ s, P s = true → tmul s s = (0, 0, 0)) →
    (∃ s, P s = true ∧ s ≠ (0, 0, 0)) →
    ((Finset.univ.filter fun s => P s = true).card = 2 ∧
      (Finset.univ.filter fun v : Fin 3 → ZMod 2 =>
        ∀ s, P s = true → unitri s.1 s.2.1 s.2.2 *ᵥ v = v).card = 4 ∧
      (Finset.univ.filter fun w : Fin 3 → ZMod 2 =>
        ∀ s, P s = true → w ᵥ* unitri s.1 s.2.1 s.2.2 = w).card = 4) ∨
    ((Finset.univ.filter fun s => P s = true).card = 4 ∧
      (((Finset.univ.filter fun v : Fin 3 → ZMod 2 =>
        ∀ s, P s = true → unitri s.1 s.2.1 s.2.2 *ᵥ v = v).card = 4 ∧
      (Finset.univ.filter fun w : Fin 3 → ZMod 2 =>
        ∀ s, P s = true → w ᵥ* unitri s.1 s.2.1 s.2.2 = w).card = 2) ∨
      ((Finset.univ.filter fun v : Fin 3 → ZMod 2 =>
        ∀ s, P s = true → unitri s.1 s.2.1 s.2.2 *ᵥ v = v).card = 2 ∧
      (Finset.univ.filter fun w : Fin 3 → ZMod 2 =>
        ∀ s, P s = true → w ᵥ* unitri s.1 s.2.1 s.2.2 = w).card = 4))) := by
  decide +kernel

theorem finrank_eq_of_natCard_eq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {n : ℕ} (h : Nat.card W = 2 ^ n) : finrank (ZMod 2) W = n :=
  Nat.pow_right_injective le_rfl ((FiniteField.pow_finrank_eq_natCard 2 W).trans h)

theorem core_sylowT {K : Subgroup (GL (Fin 3) (ZMod 2))} (hKT : K ≤ sylowT)
    (hsq : ∀ k ∈ K, k * k = 1) (hK : K ≠ ⊥) :
    (Nat.card K = 2 ∧ finrank (ZMod 2) (fixCol K) = 2 ∧ finrank (ZMod 2) (fixRow K) = 2) ∨
    (Nat.card K = 4 ∧
      ((finrank (ZMod 2) (fixCol K) = 2 ∧ finrank (ZMod 2) (fixRow K) = 1) ∨
        (finrank (ZMod 2) (fixCol K) = 1 ∧ finrank (ZMod 2) (fixRow K) = 2))) := by
  classical
  set P : ZMod 2 × ZMod 2 × ZMod 2 → Bool := fun s => decide (tGL s ∈ K) with hPdef
  have hP : ∀ s, P s = true ↔ tGL s ∈ K := fun s => decide_eq_true_iff
  have hmemK : ∀ k ∈ K, ∃ s, k = tGL s := fun k hk => by
    obtain ⟨a, b, c, rfl⟩ := hKT hk
    exact ⟨(a, b, c), rfl⟩
  have h0 : P (0, 0, 0) = true := (hP _).2 (by rw [tGL_zero]; exact K.one_mem)
  have hmul : ∀ s s', P s = true → P s' = true → P (tmul s s') = true := fun s s' hs hs' =>
    (hP _).2 (tGL_mul s s' ▸ K.mul_mem ((hP s).1 hs) ((hP s').1 hs'))
  have hsq' : ∀ s, P s = true → tmul s s = (0, 0, 0) := fun s hs =>
    tGL_injective (by rw [← tGL_mul, hsq _ ((hP s).1 hs), tGL_zero])
  have hne : ∃ s, P s = true ∧ s ≠ (0, 0, 0) := by
    obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK
    obtain ⟨s, hs⟩ := hmemK k k.2
    refine ⟨s, (hP s).2 (hs ▸ k.2), fun h => hk1 (Subtype.ext ?_)⟩
    rw [hs, h, tGL_zero]
    rfl
  have hcardK : Nat.card K = (Finset.univ.filter fun s => P s = true).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun s : {s // P s = true} => (⟨tGL s.1, (hP s.1).1 s.2⟩ : K)) ⟨fun s s' h => ?_,
        fun k => ?_⟩)).symm
    · exact Subtype.ext (tGL_injective (congrArg Subtype.val h))
    · obtain ⟨s, hs⟩ := hmemK k k.2
      exact ⟨⟨s, (hP s).2 (hs ▸ k.2)⟩, Subtype.ext hs.symm⟩
  have hcol : ∀ v, v ∈ fixCol K ↔ ∀ s, P s = true → unitri s.1 s.2.1 s.2.2 *ᵥ v = v :=
    fun v => ⟨fun hv s hs => hv _ ((hP s).1 hs), fun hv k hk => by
      obtain ⟨s, rfl⟩ := hmemK k hk
      exact hv s ((hP s).2 hk)⟩
  have hrow : ∀ w, w ∈ fixRow K ↔ ∀ s, P s = true → w ᵥ* unitri s.1 s.2.1 s.2.2 = w :=
    fun w => ⟨fun hw s hs => hw _ ((hP s).1 hs), fun hw k hk => by
      obtain ⟨s, rfl⟩ := hmemK k hk
      exact hw s ((hP s).2 hk)⟩
  have hcardV : Nat.card (fixCol K) = (Finset.univ.filter fun v : Fin 3 → ZMod 2 =>
      ∀ s, P s = true → unitri s.1 s.2.1 s.2.2 *ᵥ v = v).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight hcol)
  have hcardD : Nat.card (fixRow K) = (Finset.univ.filter fun w : Fin 3 → ZMod 2 =>
      ∀ s, P s = true → w ᵥ* unitri s.1 s.2.1 s.2.2 = w).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight hrow)
  rcases core_cards P h0 hmul hsq' hne with ⟨h1, h2, h3⟩ | ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩
  · exact Or.inl ⟨hcardK.trans h1, finrank_eq_of_natCard_eq (n := 2) (hcardV.trans h2),
      finrank_eq_of_natCard_eq (n := 2) (hcardD.trans h3)⟩
  · exact Or.inr ⟨hcardK.trans h1, Or.inl ⟨finrank_eq_of_natCard_eq (n := 2) (hcardV.trans h2),
      finrank_eq_of_natCard_eq (n := 1) (hcardD.trans h3)⟩⟩
  · exact Or.inr ⟨hcardK.trans h1, Or.inr ⟨finrank_eq_of_natCard_eq (n := 1) (hcardV.trans h2),
      finrank_eq_of_natCard_eq (n := 2) (hcardD.trans h3)⟩⟩

noncomputable abbrev regPhi : (sylowT → ZMod 2) →ₗ[ZMod 2] traceZero :=
  Fintype.linearCombination (ZMod 2) conjFamily

theorem regPhi_equivariant (h : sylowT) (f : sylowT → ZMod 2) :
    ((regPhi fun x => f (h⁻¹ * x) : traceZero) : Mat3) = conjLin h (regPhi f) :=
  trace_zero_regular_Sylow_module.2.2.2 h f

theorem regPhi_mem_fixTr_iff {K : Subgroup (GL (Fin 3) (ZMod 2))} (hKT : K ≤ sylowT)
    (f : sylowT → ZMod 2) :
    ((regPhi f : traceZero) : Mat3) ∈ fixTr K ↔
      ∀ h : sylowT, (h : GL (Fin 3) (ZMod 2)) ∈ K → ∀ x, f (h⁻¹ * x) = f x := by
  have hΦ : Function.Injective regPhi := trace_zero_regular_Sylow_module.2.2.1.1
  constructor
  · rintro ⟨-, hfix⟩ h hh x
    have h1 : regPhi (fun x => f (h⁻¹ * x)) = regPhi f :=
      Subtype.ext ((regPhi_equivariant h f).trans (hfix _ hh))
    exact congrFun (hΦ h1) x
  · intro hinv
    refine ⟨(regPhi f).2, fun k hk => ?_⟩
    have h1 := regPhi_equivariant ⟨k, hKT hk⟩ f
    have h2 : (fun x => f ((⟨k, hKT hk⟩ : sylowT)⁻¹ * x)) = f := funext (hinv _ hk)
    rw [h2] at h1
    exact h1.symm

@[expose] def invFun (K : Subgroup (GL (Fin 3) (ZMod 2))) :
    Submodule (ZMod 2) (sylowT → ZMod 2) where
  carrier := {f | ∀ h : sylowT, (h : GL (Fin 3) (ZMod 2)) ∈ K → ∀ x, f (h⁻¹ * x) = f x}
  add_mem' := fun {f g} hf hg h hh x => by simp only [Pi.add_apply, hf h hh x, hg h hh x]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c f hf h hh x => by simp only [Pi.smul_apply, hf h hh x]

theorem finrank_fixTr_mul_card {K : Subgroup (GL (Fin 3) (ZMod 2))} (hKT : K ≤ sylowT) :
    finrank (ZMod 2) (fixTr K) * Nat.card K = 8 := by
  classical
  have hΦ : Function.Bijective regPhi := trace_zero_regular_Sylow_module.2.2.1
  have hmap : (invFun K).map (traceZero.subtype ∘ₗ regPhi) = fixTr K := by
    ext X
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (regPhi_mem_fixTr_iff hKT f).2 hf
    · intro hX
      obtain ⟨f, hf⟩ := hΦ.2 ⟨X, hX.1⟩
      have hX' : ((regPhi f : traceZero) : Mat3) ∈ fixTr K := by rw [hf]; exact hX
      exact ⟨f, (regPhi_mem_fixTr_iff hKT f).1 hX', by
        rw [LinearMap.comp_apply, hf]
        rfl⟩
  have h1 : finrank (ZMod 2) (fixTr K) = finrank (ZMod 2) (invFun K) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective (traceZero.subtype ∘ₗ regPhi)
      (fun x y h => hΦ.1 (traceZero.injective_subtype h)) _).finrank_eq.symm
  set H : Subgroup sylowT := K.subgroupOf sylowT with hHdef
  set Ξ : (Quotient (QuotientGroup.rightRel H) → ZMod 2) →ₗ[ZMod 2] (sylowT → ZMod 2) :=
    LinearMap.funLeft (ZMod 2) (ZMod 2) (Quotient.mk (QuotientGroup.rightRel H))
  have hΞ : Function.Injective Ξ :=
    LinearMap.funLeft_injective_of_surjective _ _ _ Quotient.mk_surjective
  have hrange : LinearMap.range Ξ = invFun K := by
    ext f
    constructor
    · rintro ⟨f', rfl⟩ h hh x
      change f' (Quotient.mk _ (h⁻¹ * x)) = f' (Quotient.mk _ x)
      refine congrArg f' (Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_))
      have hx : x * (h⁻¹ * x)⁻¹ = h := by group
      rw [hx]
      exact hh
    · intro hf
      refine ⟨Quotient.lift f fun a b hab => ?_, funext fun x => rfl⟩
      have hab' : b * a⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hab
      have h := hf (b * a⁻¹) hab' b
      have he : (b * a⁻¹)⁻¹ * b = a := by group
      rw [he] at h
      exact h
  have h2 : finrank (ZMod 2) (invFun K) = Fintype.card (Quotient (QuotientGroup.rightRel H)) := by
    rw [← hrange, LinearMap.finrank_range_of_inj hΞ, Module.finrank_fintype_fun_eq_card]
  have h3 : Fintype.card (Quotient (QuotientGroup.rightRel H)) = H.index := by
    rw [Subgroup.index, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)
  have h4 : Nat.card H = Nat.card K := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKT).toEquiv
  rw [h1, h2, h3, ← h4, H.index_mul_card, card_sylowT]
  norm_num

theorem card_GL3 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field (𝔽 := ZMod 2) 3, ZMod.card, Fin.prod_univ_three]
  norm_num

theorem exists_conj_le_sylowT {K : Subgroup (GL (Fin 3) (ZMod 2))} (hK : IsPGroup 2 K) :
    ∃ g : GL (Fin 3) (ZMod 2), ∀ k ∈ K, g⁻¹ * k * g ∈ sylowT := by
  have hindex : sylowT.index = 21 := by
    have h := sylowT.index_mul_card
    rw [card_sylowT, card_GL3] at h
    omega
  have hodd : ¬ 2 ∣ Nat.card (GL (Fin 3) (ZMod 2) ⧸ sylowT) := by
    rw [← Subgroup.index, hindex]
    norm_num
  obtain ⟨q, hq⟩ := hK.nonempty_fixed_point_of_prime_not_dvd_card _ hodd
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, fun k hk => ?_⟩
  have h := hq ⟨k⁻¹, K.inv_mem hk⟩
  change (QuotientGroup.mk (k⁻¹ * g) : GL (Fin 3) (ZMod 2) ⧸ sylowT) = QuotientGroup.mk g at h
  rw [QuotientGroup.eq] at h
  simpa [mul_assoc] using h

abbrev conjSubgroup (g : GL (Fin 3) (ZMod 2)) (K : Subgroup (GL (Fin 3) (ZMod 2))) :
    Subgroup (GL (Fin 3) (ZMod 2)) :=
  K.map (MulAut.conj g).toMonoidHom

theorem conj_mem_conjSubgroup (g : GL (Fin 3) (ZMod 2)) {K : Subgroup (GL (Fin 3) (ZMod 2))}
    {k : GL (Fin 3) (ZMod 2)} (hk : k ∈ K) : g * k * g⁻¹ ∈ conjSubgroup g K :=
  ⟨k, hk, rfl⟩

theorem exists_of_mem_conjSubgroup {g : GL (Fin 3) (ZMod 2)} {K : Subgroup (GL (Fin 3) (ZMod 2))}
    {k : GL (Fin 3) (ZMod 2)} (hk : k ∈ conjSubgroup g K) : ∃ k' ∈ K, k = g * k' * g⁻¹ := by
  obtain ⟨k', hk', rfl⟩ := hk
  exact ⟨k', hk', rfl⟩

theorem finrank_eq_of_mem_iff {W₁ W₂ : Type*} [AddCommGroup W₁] [Module (ZMod 2) W₁]
    [AddCommGroup W₂] [Module (ZMod 2) W₂] (e : W₁ ≃ₗ[ZMod 2] W₂) {S₁ : Submodule (ZMod 2) W₁}
    {S₂ : Submodule (ZMod 2) W₂} (h : ∀ w, w ∈ S₁ ↔ e w ∈ S₂) :
    finrank (ZMod 2) S₁ = finrank (ZMod 2) S₂ := by
  have hmap : S₁.map (e : W₁ →ₗ[ZMod 2] W₂) = S₂ := by
    ext w
    refine ⟨?_, fun hw => ⟨e.symm w, (h _).2 (by rwa [e.apply_symm_apply]), e.apply_symm_apply w⟩⟩
    rintro ⟨w', hw', rfl⟩
    exact (h w').1 hw'
  rw [← hmap]
  exact (e.submoduleMap S₁).finrank_eq

theorem conj_mulVec (g k : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    ((g * k * g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ ((g : Mat3) *ᵥ v) =
      (g : Mat3) *ᵥ ((k : Mat3) *ᵥ v) := by
  rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]

theorem conj_vecMul (g k : GL (Fin 3) (ZMod 2)) (w : Fin 3 → ZMod 2) :
    (w ᵥ* ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3)) ᵥ* ((g * k * g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) =
      (w ᵥ* (k : Mat3)) ᵥ* ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) := by
  rw [vecMul_vecMul, vecMul_vecMul, ← Units.val_mul, ← Units.val_mul]
  congr 2
  group

theorem conjLin_conj (g k : GL (Fin 3) (ZMod 2)) (X : Mat3) :
    conjLin (g * k * g⁻¹) (conjLin g X) = conjLin g (conjLin k X) := by
  rw [← conjLin_mul, ← conjLin_mul, inv_mul_cancel_right]

@[expose] def mulVecEquiv (g : GL (Fin 3) (ZMod 2)) :
    (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun v := (g : Mat3) *ᵥ v
  map_add' v w := mulVec_add _ v w
  map_smul' c v := mulVec_smul _ c v
  invFun v := ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ v
  left_inv v := by
    change _ *ᵥ (_ *ᵥ v) = v
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  right_inv v := by
    change _ *ᵥ (_ *ᵥ v) = v
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

@[expose] def vecMulEquiv (g : GL (Fin 3) (ZMod 2)) :
    (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun w := w ᵥ* ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3)
  map_add' v w := add_vecMul _ v w
  map_smul' c w := smul_vecMul c w _
  invFun w := w ᵥ* (g : Mat3)
  left_inv w := by
    change (w ᵥ* _) ᵥ* _ = w
    rw [vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
  right_inv w := by
    change (w ᵥ* _) ᵥ* _ = w
    rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]

@[expose] def conjEquiv (g : GL (Fin 3) (ZMod 2)) : Mat3 ≃ₗ[ZMod 2] Mat3 where
  toFun X := conjLin g X
  map_add' X Y := map_add _ X Y
  map_smul' c X := map_smul _ c X
  invFun X := conjLin g⁻¹ X
  left_inv X := by
    change conjLin g⁻¹ (conjLin g X) = X
    rw [← conjLin_mul, inv_mul_cancel, conjLin_one]
  right_inv X := by
    change conjLin g (conjLin g⁻¹ X) = X
    rw [← conjLin_mul, mul_inv_cancel, conjLin_one]

theorem finrank_fixCol_conj (g : GL (Fin 3) (ZMod 2)) (K : Subgroup (GL (Fin 3) (ZMod 2))) :
    finrank (ZMod 2) (fixCol (conjSubgroup g K)) = finrank (ZMod 2) (fixCol K) := by
  refine (finrank_eq_of_mem_iff (S₁ := fixCol K) (S₂ := fixCol (conjSubgroup g K))
    (mulVecEquiv g) fun v => ⟨fun hv k hk => ?_, fun hv k hk => ?_⟩).symm
  · obtain ⟨k', hk', rfl⟩ := exists_of_mem_conjSubgroup hk
    change _ *ᵥ ((g : Mat3) *ᵥ v) = (g : Mat3) *ᵥ v
    rw [conj_mulVec, hv k' hk']
  · have h := hv _ (conj_mem_conjSubgroup g hk)
    change _ *ᵥ ((g : Mat3) *ᵥ v) = (g : Mat3) *ᵥ v at h
    rw [conj_mulVec] at h
    exact (mulVecEquiv g).injective h

theorem finrank_fixRow_conj (g : GL (Fin 3) (ZMod 2)) (K : Subgroup (GL (Fin 3) (ZMod 2))) :
    finrank (ZMod 2) (fixRow (conjSubgroup g K)) = finrank (ZMod 2) (fixRow K) := by
  refine (finrank_eq_of_mem_iff (S₁ := fixRow K) (S₂ := fixRow (conjSubgroup g K))
    (vecMulEquiv g) fun w => ⟨fun hw k hk => ?_, fun hw k hk => ?_⟩).symm
  · obtain ⟨k', hk', rfl⟩ := exists_of_mem_conjSubgroup hk
    change (w ᵥ* _) ᵥ* _ = w ᵥ* _
    rw [conj_vecMul, hw k' hk']
  · have h := hw _ (conj_mem_conjSubgroup g hk)
    change (w ᵥ* _) ᵥ* _ = w ᵥ* _ at h
    rw [conj_vecMul] at h
    exact (vecMulEquiv g).injective h

theorem finrank_fixTr_conj (g : GL (Fin 3) (ZMod 2)) (K : Subgroup (GL (Fin 3) (ZMod 2))) :
    finrank (ZMod 2) (fixTr (conjSubgroup g K)) = finrank (ZMod 2) (fixTr K) := by
  refine (finrank_eq_of_mem_iff (S₁ := fixTr K) (S₂ := fixTr (conjSubgroup g K))
    (conjEquiv g) fun X => ⟨fun hX => ?_, fun hX => ?_⟩).symm
  · refine ⟨conjLin_mem g hX.1, fun k hk => ?_⟩
    obtain ⟨k', hk', rfl⟩ := exists_of_mem_conjSubgroup hk
    change conjLin _ (conjLin g X) = conjLin g X
    rw [conjLin_conj, hX.2 k' hk']
  · refine ⟨?_, fun k hk => ?_⟩
    · have h := conjLin_mem g⁻¹ hX.1
      change conjLin g⁻¹ (conjLin g X) ∈ traceZero at h
      rwa [← conjLin_mul, inv_mul_cancel, conjLin_one] at h
    · have h := hX.2 _ (conj_mem_conjSubgroup g hk)
      change conjLin _ (conjLin g X) = conjLin g X at h
      rw [conjLin_conj] at h
      exact (conjEquiv g).injective h

section Abstract

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def toGL (β : Module.Basis (Fin 3) (ZMod 2) V) :
    (V ≃ₗ[ZMod 2] V) →* GL (Fin 3) (ZMod 2) where
  toFun b := ⟨LinearMap.toMatrix β β b, LinearMap.toMatrix β β b.symm,
    by rw [← LinearMap.toMatrix_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix_id],
    by rw [← LinearMap.toMatrix_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix_id]⟩
  map_one' := Units.ext (LinearMap.toMatrix_id β)
  map_mul' b c := Units.ext (LinearMap.toMatrix_comp β β β (b : V →ₗ[ZMod 2] V) c)

theorem coe_toGL (β : Module.Basis (Fin 3) (ZMod 2) V) (b : V ≃ₗ[ZMod 2] V) :
    (toGL β b : Mat3) = LinearMap.toMatrix β β b :=
  rfl

theorem coe_toGL_inv (β : Module.Basis (Fin 3) (ZMod 2) V) (b : V ≃ₗ[ZMod 2] V) :
    (((toGL β b)⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) = LinearMap.toMatrix β β b.symm :=
  rfl

theorem toGL_injective (β : Module.Basis (Fin 3) (ZMod 2) V) : Function.Injective (toGL β) :=
  fun _ _ h => LinearEquiv.toLinearMap_injective
    ((LinearMap.toMatrix β β).injective (congrArg Units.val h))

theorem equivFun_apply_toGL (β : Module.Basis (Fin 3) (ZMod 2) V) (b : V ≃ₗ[ZMod 2] V) (v : V) :
    β.equivFun (b v) = (toGL β b : Mat3) *ᵥ β.equivFun v := by
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, coe_toGL,
    LinearMap.toMatrix_mulVec_repr]
  rfl

theorem dualBasis_equivFun_comp (β : Module.Basis (Fin 3) (ZMod 2) V)
    (f : Module.Dual (ZMod 2) V) (c : V →ₗ[ZMod 2] V) :
    β.dualBasis.equivFun (f ∘ₗ c) = β.dualBasis.equivFun f ᵥ* LinearMap.toMatrix β β c := by
  funext j
  rw [Module.Basis.dualBasis_equivFun, LinearMap.comp_apply, vecMul, dotProduct]
  simp only [Module.Basis.dualBasis_equivFun, LinearMap.toMatrix_apply]
  conv_lhs => rw [← β.sum_repr (c (β j))]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]

theorem finrank_fixedVec (β : Module.Basis (Fin 3) (ZMod 2) V) (B : Subgroup (V ≃ₗ[ZMod 2] V)) :
    finrank (ZMod 2) (fixedVec B) = finrank (ZMod 2) (fixCol (B.map (toGL β))) := by
  refine finrank_eq_of_mem_iff β.equivFun fun v => ⟨fun hv k hk => ?_, fun hv b hb => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := hk
    rw [← equivFun_apply_toGL, hv b hb]
  · have h := hv _ ⟨b, hb, rfl⟩
    rw [← equivFun_apply_toGL] at h
    exact β.equivFun.injective h

theorem finrank_fixedDual (β : Module.Basis (Fin 3) (ZMod 2) V)
    (B : Subgroup (V ≃ₗ[ZMod 2] V)) :
    finrank (ZMod 2) (fixedDual B) = finrank (ZMod 2) (fixRow (B.map (toGL β))) := by
  refine finrank_eq_of_mem_iff β.dualBasis.equivFun fun f => ⟨fun hf k hk => ?_, fun hf b hb => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := hk
    have h := hf b⁻¹ (B.inv_mem hb)
    change f ∘ₗ (b : V →ₗ[ZMod 2] V) = f at h
    rw [coe_toGL, ← dualBasis_equivFun_comp]
    exact congrArg β.dualBasis.equivFun h
  · have h := hf _ ⟨b⁻¹, B.inv_mem hb, rfl⟩
    rw [coe_toGL, ← dualBasis_equivFun_comp] at h
    change f ∘ₗ (b.symm : V →ₗ[ZMod 2] V) = f
    exact β.dualBasis.equivFun.injective h

theorem finrank_fixedTraceZeroEnd (β : Module.Basis (Fin 3) (ZMod 2) V)
    (B : Subgroup (V ≃ₗ[ZMod 2] V)) :
    finrank (ZMod 2) (fixedTraceZeroEnd B) = finrank (ZMod 2) (fixTr (B.map (toGL β))) := by
  have htr : ∀ X : Module.End (ZMod 2) V,
      X ∈ traceZeroEnd V ↔ LinearMap.toMatrix β β X ∈ traceZero := fun X => by
    rw [traceZeroEnd, traceZero, LinearMap.mem_ker, LinearMap.mem_ker,
      LinearMap.trace_eq_matrix_trace (ZMod 2) β, Matrix.traceLinearMap_apply]
  have hconj : ∀ (b : V ≃ₗ[ZMod 2] V) (X : Module.End (ZMod 2) V),
      LinearMap.toMatrix β β ((b : V →ₗ[ZMod 2] V) ∘ₗ X ∘ₗ (b.symm : V →ₗ[ZMod 2] V)) =
        conjLin (toGL β b) (LinearMap.toMatrix β β X) := fun b X => by
    rw [conjLin_apply, coe_toGL, coe_toGL_inv, LinearMap.toMatrix_comp β β β,
      LinearMap.toMatrix_comp β β β, Matrix.mul_assoc]
  refine finrank_eq_of_mem_iff (LinearMap.toMatrix β β) fun X =>
    ⟨fun hX => ⟨(htr X).1 hX.1, fun k hk => ?_⟩, fun hX => ⟨(htr X).2 hX.1, fun b hb => ?_⟩⟩
  · obtain ⟨b, hb, rfl⟩ := hk
    rw [← hconj, hX.2 b hb]
  · have h := hX.2 _ ⟨b, hb, rfl⟩
    rw [← hconj] at h
    exact (LinearMap.toMatrix β β).injective h

end Abstract

end FixedCodim

open FixedCodim in
theorem GL3_elementary_abelian_fixed_codimensions {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (hV : finrank (ZMod 2) V = 3) (B : Subgroup (V ≃ₗ[ZMod 2] V))
    (hBe : CFSG.Open.IsElemAbelian 2 B) (hB : B ≠ ⊥) (r : ℕ) (hr : Nat.card B = 2 ^ r) :
    (r = 1 ∨ r = 2) ∧
    (r = 1 → (finrank (ZMod 2) V - finrank (ZMod 2) (fixedVec B),
      finrank (ZMod 2) (Module.Dual (ZMod 2) V) - finrank (ZMod 2) (fixedDual B)) = (1, 1)) ∧
    (r = 2 → (finrank (ZMod 2) V - finrank (ZMod 2) (fixedVec B),
        finrank (ZMod 2) (Module.Dual (ZMod 2) V) - finrank (ZMod 2) (fixedDual B)) = (1, 2) ∨
      (finrank (ZMod 2) V - finrank (ZMod 2) (fixedVec B),
        finrank (ZMod 2) (Module.Dual (ZMod 2) V) - finrank (ZMod 2) (fixedDual B)) = (2, 1)) ∧
    finrank (ZMod 2) (traceZeroEnd V) - finrank (ZMod 2) (fixedTraceZeroEnd B) =
      8 - 8 / Nat.card B := by
  have : Module.Finite (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype V := Fintype.ofFinite V
  set β := Module.finBasisOfFinrankEq (ZMod 2) V hV
  set K₀ := B.map (toGL β)
  have hK₀ : Nat.card K₀ = Nat.card B := Subgroup.card_map_of_injective (toGL_injective β)
  obtain ⟨g, hg⟩ := exists_conj_le_sylowT (K := K₀) (IsPGroup.of_card (hK₀.trans hr))
  set K := conjSubgroup g⁻¹ K₀
  have hKT : K ≤ sylowT := by
    rintro _ ⟨k, hk, rfl⟩
    change g⁻¹ * k * g⁻¹⁻¹ ∈ sylowT
    rw [inv_inv]
    exact hg k hk
  have hKcard : Nat.card K = Nat.card B :=
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).trans hK₀
  have hKsq : ∀ k ∈ K, k * k = 1 := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hb2 : b * b = 1 := by rw [← pow_two]; exact hBe.2 b hb
    rw [← map_mul, ← map_mul, hb2, map_one, map_one]
  have hKne : K ≠ ⊥ := fun h => hB (Subgroup.eq_bot_of_card_eq B (by
    rw [← hKcard, h, Subgroup.card_bot]))
  have hdV : finrank (ZMod 2) (fixedVec B) = finrank (ZMod 2) (fixCol K) :=
    (finrank_fixedVec β B).trans (finrank_fixCol_conj g⁻¹ K₀).symm
  have hdD : finrank (ZMod 2) (fixedDual B) = finrank (ZMod 2) (fixRow K) :=
    (finrank_fixedDual β B).trans (finrank_fixRow_conj g⁻¹ K₀).symm
  have hdA : finrank (ZMod 2) (fixedTraceZeroEnd B) = finrank (ZMod 2) (fixTr K) :=
    (finrank_fixedTraceZeroEnd β B).trans (finrank_fixTr_conj g⁻¹ K₀).symm
  have hA := finrank_fixTr_mul_card hKT
  rw [hKcard] at hA
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hr]; positivity)
  have hAdiv : finrank (ZMod 2) (fixTr K) = 8 / Nat.card B := by
    rw [← hA, Nat.mul_div_cancel _ Nat.card_pos]
  have hV' : finrank (ZMod 2) (Module.Dual (ZMod 2) V) = 3 := by
    rw [Subspace.dual_finrank_eq, hV]
  rw [hdV, hdD, hdA, hV, hV', finrank_traceZeroEnd hV, hAdiv]
  rcases core_sylowT hKT hKsq hKne with ⟨h1, h2, h3⟩ | ⟨h1, h23⟩
  · rw [hKcard, hr] at h1
    have hr1 : r = 1 := Nat.pow_right_injective le_rfl (h1.trans (pow_one 2).symm)
    exact ⟨Or.inl hr1, fun _ => by rw [h2, h3], fun h => by omega, rfl⟩
  · rw [hKcard, hr] at h1
    have hr2 : r = 2 := Nat.pow_right_injective le_rfl (h1.trans (by norm_num))
    refine ⟨Or.inr hr2, fun h => by omega, fun _ => ?_, rfl⟩
    rcases h23 with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · left
      rw [h2, h3]
    · right
      rw [h2, h3]

end CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
