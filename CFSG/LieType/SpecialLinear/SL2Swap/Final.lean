module

public import CFSG.LieType.SpecialLinear.SL2Swap.Collapse
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ5
public import CFSG.LieType.SpecialLinear.SL2Swap.Basic
public import CFSG.LieType.SpecialLinear.SL2Swap.Faithful

public section

namespace CFSG.LieType.SpecialLinear

open scoped MatrixGroups
open CFSG.LinearGroups CFSG.LocalAnalysis.EvenBN.Common
open CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.QuasithinUnique.Setup.Layer
open CFSG.QuasithinUnique.Setup.Offender
open CFSG.Quasithin.B6

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable {Z : Type} [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z]

instance finiteGL (Z : Type) [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z] :
    Finite (Z ≃ₗ[ZMod 2] Z) :=
  Finite.of_injective (fun f : Z ≃ₗ[ZMod 2] Z => (f : Z → Z))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

@[expose] noncomputable def glEquiv (Z : Type) [AddCommGroup Z] [Module (ZMod 2) Z] :
    (Module.End (ZMod 2) Z)ˣ ≃* (Z ≃ₗ[ZMod 2] Z) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Z

@[expose] noncomputable def repLin {G : Type*} [Group G]
    (ρ : Representation (ZMod 2) G Z) : G →* (Z ≃ₗ[ZMod 2] Z) :=
  (glEquiv Z).toMonoidHom.comp ρ.toHomUnits

omit [Finite Z] in
theorem repLin_apply {G : Type*} [Group G] (ρ : Representation (ZMod 2) G Z) (g : G) (z : Z) :
    repLin ρ g z = ρ g z := rfl

omit [Finite Z] in
theorem repLin_injective {G : Type*} [Group G] (ρ : Representation (ZMod 2) G Z)
    (hρ : Function.Injective ρ) : Function.Injective (repLin ρ) := by
  intro a b h
  have h1 := (glEquiv Z).injective h
  apply hρ
  have h2 := congrArg Units.val h1
  simpa [MonoidHom.coe_toHomUnits] using h2

@[expose] noncomputable def factorHom (ρ : Representation (ZMod 2) (SL(2, F) × SL(2, F)) Z)
    (i : Fin 2) : SL(2, F) →* (Z ≃ₗ[ZMod 2] Z) :=
  Fin.cases (repLin ρ |>.comp (MonoidHom.inl (SL(2, F)) (SL(2, F))))
    (fun _ => repLin ρ |>.comp (MonoidHom.inr (SL(2, F)) (SL(2, F)))) i

omit [Fintype F] [CharP F 2] [Finite Z] in
@[simp]
theorem factorHom_zero (ρ : Representation (ZMod 2) (SL(2, F) × SL(2, F)) Z)
    (g : SL(2, F)) : factorHom ρ 0 g = repLin ρ (g, 1) := rfl

omit [Fintype F] [CharP F 2] [Finite Z] in
@[simp]
theorem factorHom_one (ρ : Representation (ZMod 2) (SL(2, F) × SL(2, F)) Z)
    (g : SL(2, F)) : factorHom ρ 1 g = repLin ρ (1, g) := rfl

@[expose] noncomputable def factorSub (ρ : Representation (ZMod 2) (SL(2, F) × SL(2, F)) Z)
    (i : Fin 2) : Subgroup (Z ≃ₗ[ZMod 2] Z) :=
  (factorHom ρ i).range

@[expose] noncomputable def sectionLin {D : Type*} [Group D]
    (δ : Representation (ZMod 2) D Z) : D →* (Z ≃ₗ[ZMod 2] Z) :=
  (glEquiv Z).toMonoidHom.comp δ.toHomUnits

omit [Finite Z] in
theorem sectionLin_apply {D : Type*} [Group D] (δ : Representation (ZMod 2) D Z) (d : D)
    (z : Z) : sectionLin δ d z = δ d z := rfl

@[expose] noncomputable def sectionSub {D : Type*} [Group D]
    (δ : Representation (ZMod 2) D Z) : Subgroup (Z ≃ₗ[ZMod 2] Z) :=
  (sectionLin δ).range

theorem sl2Pair_swap_false (hq : 4 ≤ Fintype.card F)
    (ρ : Representation (ZMod 2) (SL(2, F) × SL(2, F)) Z) [Fact ρ.IsIrreducible]
    (h₁ : ∃ g, ρ (g, 1) ≠ 1) (h₂ : ∃ g, ρ (1, g) ≠ 1)
    {D : Type} [Group D] [Finite D] (δ : Representation (ZMod 2) D Z)
    (hD2 : ∀ d, δ d * δ d = 1)
    (hquad : ∀ a b z, δ b (δ a z - z) = δ a z - z)
    (hoff : Nat.card Z * Nat.card δ.ker ≤
      Nat.card D * Nat.card {z : Z // ∀ d, δ d z = z})
    (hcompat : ∀ d, ∃ (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F) (sw : Bool),
      ∀ m z, δ d (ρ m z) = ρ (pairAut A₁ A₂ σ sw m) (δ d z))
    (hswap : ∃ x, ∃ (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F),
      ∀ m z, δ x (ρ m z) = ρ (pairAut A₁ A₂ σ true m) (δ x z)) :
    False := by
  classical
  have : Nontrivial Z := ((isIrreducible_iff ρ).mp Fact.out).1
  have hker : ρ.ker = ⊥ := ker_eq_bot_of_factor_nontrivial hq ρ h₁ h₂
  have hρin : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hker
  have hrepLin_inj : Function.Injective (repLin ρ) := repLin_injective ρ hρin
  obtain ⟨s4, hs4⟩ := exists_finset_card_four_of_card (F := F) hq
  have : Group.IsPerfect (SL(2, F)) := special_linear_dimension_two_perfect ⟨s4, hs4⟩
  have : Nontrivial (SL(2, F)) :=
    (sl2_isSimpleGroup_of_charTwo (by simpa [Nat.card_eq_fintype_card] using hq)).toNontrivial
  have hfac_inj : ∀ i, Function.Injective (factorHom ρ i) := by
    intro i
    fin_cases i
    · intro g h hgh
      have hpair := hrepLin_inj hgh
      exact congrArg Prod.fst hpair
    · intro g h hgh
      have hpair := hrepLin_inj hgh
      exact congrArg Prod.snd hpair
  have hLperf : ∀ i, Group.IsPerfect (factorSub ρ i) := by
    intro i
    exact Group.IsPerfect.range (factorHom ρ i)
  have hLnt : ∀ i, Nontrivial (factorSub ρ i) := by
    intro i
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    obtain ⟨g, hg⟩ := exists_ne (1 : SL(2, F))
    have hg' : factorHom ρ i g ≠ 1 := by
      intro h
      apply hg
      apply hfac_inj i
      simpa using h
    have hmem : factorHom ρ i g ∈ factorSub ρ i := ⟨g, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hg' hmem
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ factorSub ρ i, ∀ y ∈ factorSub ρ j, x * y = y * x := by
    intro i j hij x hx y hy
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      change repLin ρ (g, 1) * repLin ρ (1, h) =
        repLin ρ (1, h) * repLin ρ (g, 1)
      rw [← map_mul, ← map_mul]
      congr 1
      ext <;> simp
    · obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      change repLin ρ (1, g) * repLin ρ (h, 1) =
        repLin ρ (h, 1) * repLin ρ (1, g)
      rw [← map_mul, ← map_mul]
      congr 1
      ext <;> simp
    · exact absurd rfl hij
  have hirr : IsIrrAct (⨆ i, factorSub ρ i) := by
    intro U hU
    have hUρ : ∀ m : SL(2, F) × SL(2, F), ∀ u ∈ U, ρ m u ∈ U := by
      intro m u hu
      have hm : repLin ρ m = repLin ρ (m.1, 1) * repLin ρ (1, m.2) := by
        rw [← map_mul]
        congr 1
        ext <;> simp
      have h0 : repLin ρ (m.1, 1) ∈ factorSub ρ 0 := ⟨m.1, factorHom_zero ρ m.1⟩
      have h1 : repLin ρ (1, m.2) ∈ factorSub ρ 1 := ⟨m.2, factorHom_one ρ m.2⟩
      have hsup0 : repLin ρ (m.1, 1) ∈ ⨆ i, factorSub ρ i :=
        le_iSup (fun i => factorSub ρ i) 0 h0
      have hsup1 : repLin ρ (1, m.2) ∈ ⨆ i, factorSub ρ i :=
        le_iSup (fun i => factorSub ρ i) 1 h1
      have h2 := hU (repLin ρ (1, m.2)) hsup1 u hu
      have h3 := hU (repLin ρ (m.1, 1)) hsup0 (repLin ρ (1, m.2) u) h2
      rw [← repLin_apply, hm, LinearEquiv.mul_apply]
      exact h3
    exact ((isIrreducible_iff ρ).mp Fact.out).2 U hUρ
  have hcard_fac : ∀ i, Nat.card (factorSub ρ i) = Nat.card (SL(2, F)) := by
    intro i
    exact Nat.card_congr (MonoidHom.ofInjective (hfac_inj i)).symm.toEquiv
  have hcard_conj : ∀ (a : Z ≃ₗ[ZMod 2] Z) (X : Subgroup (Z ≃ₗ[ZMod 2] Z)),
      Nat.card (conjSub a X) = Nat.card X := by
    intro a X
    rw [conjSub]
    exact Subgroup.card_map_of_injective (MulAut.conj a).injective
  have hconj_of_compat : ∀ (d : D) (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F) (sw : Bool),
      (∀ m z, δ d (ρ m z) = ρ (pairAut A₁ A₂ σ sw m) (δ d z)) →
      ∀ m, sectionLin δ d * repLin ρ m * (sectionLin δ d)⁻¹ =
        repLin ρ (pairAut A₁ A₂ σ sw m) := by
    intro d A₁ A₂ σ sw hd m
    apply LinearEquiv.ext
    intro z
    have h := hd m ((sectionLin δ d)⁻¹ z)
    have hz : δ d ((sectionLin δ d)⁻¹ z) = z := by
      exact (sectionLin δ d).apply_symm_apply z
    rw [hz] at h
    simpa [sectionLin_apply, repLin_apply, Module.End.mul_apply] using h
  have hle_zero_false : ∀ (d : D) (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F),
      (∀ m z, δ d (ρ m z) = ρ (pairAut A₁ A₂ σ false m) (δ d z)) →
      conjSub (sectionLin δ d) (factorSub ρ 0) ≤ factorSub ρ 0 := by
    intro d A₁ A₂ σ hd x hx
    rw [mem_conjSub] at hx
    obtain ⟨g, hg⟩ := hx
    have hx' : x = sectionLin δ d * factorHom ρ 0 g * (sectionLin δ d)⁻¹ := by
      calc x = sectionLin δ d * (sectionLin δ d)⁻¹ * x * sectionLin δ d * (sectionLin δ d)⁻¹ := by
              group
        _ = sectionLin δ d * ((sectionLin δ d)⁻¹ * x * sectionLin δ d) *
              (sectionLin δ d)⁻¹ := by group
        _ = sectionLin δ d * factorHom ρ 0 g * (sectionLin δ d)⁻¹ := by rw [hg]
    rw [hx', factorHom_zero, hconj_of_compat d A₁ A₂ σ false hd (g, 1), pairAut_false_inl]
    exact ⟨CFSG.QuasithinUnique.K1.stdAut A₁ σ 0 g, by rw [factorHom_zero]⟩
  have hle_zero_true : ∀ (d : D) (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F),
      (∀ m z, δ d (ρ m z) = ρ (pairAut A₁ A₂ σ true m) (δ d z)) →
      conjSub (sectionLin δ d) (factorSub ρ 0) ≤ factorSub ρ 1 := by
    intro d A₁ A₂ σ hd x hx
    rw [mem_conjSub] at hx
    obtain ⟨g, hg⟩ := hx
    have hx' : x = sectionLin δ d * factorHom ρ 0 g * (sectionLin δ d)⁻¹ := by
      calc x = sectionLin δ d * (sectionLin δ d)⁻¹ * x * sectionLin δ d * (sectionLin δ d)⁻¹ := by
              group
        _ = sectionLin δ d * ((sectionLin δ d)⁻¹ * x * sectionLin δ d) *
              (sectionLin δ d)⁻¹ := by group
        _ = sectionLin δ d * factorHom ρ 0 g * (sectionLin δ d)⁻¹ := by rw [hg]
    rw [hx', factorHom_zero, hconj_of_compat d A₁ A₂ σ true hd (g, 1), pairAut_true_inl]
    exact ⟨CFSG.QuasithinUnique.K1.stdAut A₂ σ 0 g, by rw [factorHom_one]⟩
  have hle_one_false : ∀ (d : D) (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F),
      (∀ m z, δ d (ρ m z) = ρ (pairAut A₁ A₂ σ false m) (δ d z)) →
      conjSub (sectionLin δ d) (factorSub ρ 1) ≤ factorSub ρ 1 := by
    intro d A₁ A₂ σ hd x hx
    rw [mem_conjSub] at hx
    obtain ⟨g, hg⟩ := hx
    have hx' : x = sectionLin δ d * factorHom ρ 1 g * (sectionLin δ d)⁻¹ := by
      calc x = sectionLin δ d * (sectionLin δ d)⁻¹ * x * sectionLin δ d * (sectionLin δ d)⁻¹ := by
              group
        _ = sectionLin δ d * ((sectionLin δ d)⁻¹ * x * sectionLin δ d) *
              (sectionLin δ d)⁻¹ := by group
        _ = sectionLin δ d * factorHom ρ 1 g * (sectionLin δ d)⁻¹ := by rw [hg]
    rw [hx', factorHom_one, hconj_of_compat d A₁ A₂ σ false hd (1, g), pairAut_false_inr]
    exact ⟨CFSG.QuasithinUnique.K1.stdAut A₂ σ 0 g, by rw [factorHom_one]⟩
  have hle_one_true : ∀ (d : D) (A₁ A₂ : GL (Fin 2) F) (σ : F ≃+* F),
      (∀ m z, δ d (ρ m z) = ρ (pairAut A₁ A₂ σ true m) (δ d z)) →
      conjSub (sectionLin δ d) (factorSub ρ 1) ≤ factorSub ρ 0 := by
    intro d A₁ A₂ σ hd x hx
    rw [mem_conjSub] at hx
    obtain ⟨g, hg⟩ := hx
    have hx' : x = sectionLin δ d * factorHom ρ 1 g * (sectionLin δ d)⁻¹ := by
      calc x = sectionLin δ d * (sectionLin δ d)⁻¹ * x * sectionLin δ d * (sectionLin δ d)⁻¹ := by
              group
        _ = sectionLin δ d * ((sectionLin δ d)⁻¹ * x * sectionLin δ d) *
              (sectionLin δ d)⁻¹ := by group
        _ = sectionLin δ d * factorHom ρ 1 g * (sectionLin δ d)⁻¹ := by rw [hg]
    rw [hx', factorHom_one, hconj_of_compat d A₁ A₂ σ true hd (1, g), pairAut_true_inr]
    exact ⟨CFSG.QuasithinUnique.K1.stdAut A₁ σ 0 g, by rw [factorHom_zero]⟩
  have hperm0 : ∀ d : D, ∃ j : Fin 2,
      conjSub (sectionLin δ d) (factorSub ρ 0) = factorSub ρ j := by
    intro d
    obtain ⟨A₁, A₂, σ, sw, hd⟩ := hcompat d
    cases sw
    · exact ⟨0, Subgroup.eq_of_le_of_card_ge (hle_zero_false d A₁ A₂ σ hd)
        (by rw [hcard_conj, hcard_fac 0])⟩
    · exact ⟨1, Subgroup.eq_of_le_of_card_ge (hle_zero_true d A₁ A₂ σ hd)
        (by rw [hcard_conj, hcard_fac 1, hcard_fac 0])⟩
  have hperm1 : ∀ d : D, ∃ j : Fin 2,
      conjSub (sectionLin δ d) (factorSub ρ 1) = factorSub ρ j := by
    intro d
    obtain ⟨A₁, A₂, σ, sw, hd⟩ := hcompat d
    cases sw
    · exact ⟨1, Subgroup.eq_of_le_of_card_ge (hle_one_false d A₁ A₂ σ hd)
        (by rw [hcard_conj, hcard_fac 1])⟩
    · exact ⟨0, Subgroup.eq_of_le_of_card_ge (hle_one_true d A₁ A₂ σ hd)
        (by rw [hcard_conj, hcard_fac 0, hcard_fac 1])⟩
  have hperm : ∀ a ∈ sectionSub δ, ∀ i : Fin 2, ∃ j : Fin 2,
      conjSub a (factorSub ρ i) = factorSub ρ j := by
    rintro a ⟨d, rfl⟩ i
    fin_cases i
    · exact hperm0 d
    · exact hperm1 d
  have htrans : ∀ i j : Fin 2, ∃ a ∈ sectionSub δ,
      conjSub a (factorSub ρ i) = factorSub ρ j := by
    intro i j
    obtain ⟨x, A₁, A₂, σ, hx⟩ := hswap
    fin_cases i <;> fin_cases j
    · exact ⟨1, one_mem _, by rw [conjSub_one]⟩
    · refine ⟨sectionLin δ x, ⟨x, rfl⟩, Subgroup.eq_of_le_of_card_ge ?_ (by
        change Nat.card (factorSub ρ 1) ≤ Nat.card (conjSub (sectionLin δ x) (factorSub ρ 0))
        rw [hcard_conj, hcard_fac 1, hcard_fac 0])⟩
      exact hle_zero_true x A₁ A₂ σ hx
    · refine ⟨sectionLin δ x, ⟨x, rfl⟩, Subgroup.eq_of_le_of_card_ge ?_ (by
        change Nat.card (factorSub ρ 0) ≤ Nat.card (conjSub (sectionLin δ x) (factorSub ρ 1))
        rw [hcard_conj, hcard_fac 0, hcard_fac 1])⟩
      exact hle_one_true x A₁ A₂ σ hx
    · exact ⟨1, one_mem _, by rw [conjSub_one]⟩
  have hA2 : ∀ a ∈ sectionSub δ, a * a = 1 := by
    rintro a ⟨d, rfl⟩
    apply LinearEquiv.ext
    intro z
    have h := congrArg (fun f : Module.End (ZMod 2) Z => f z) (hD2 d)
    simpa [sectionLin_apply, Module.End.mul_apply] using h
  have hAel : CFSG.IsElementaryAbelian 2 (sectionSub δ) := by
    refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      apply LinearEquiv.ext
      intro z
      obtain ⟨d, hd⟩ := x.2
      obtain ⟨e, he⟩ := y.2
      show (x.1 * y.1) z = (y.1 * x.1) z
      rw [← hd, ← he]
      have h1 : sectionLin δ d ((sectionLin δ e) z - z) = (sectionLin δ e) z - z := by
        simpa [sectionLin_apply] using hquad e d z
      have h2 : sectionLin δ e ((sectionLin δ d) z - z) = (sectionLin δ d) z - z := by
        simpa [sectionLin_apply] using hquad d e z
      calc sectionLin δ d ((sectionLin δ e) z) =
            sectionLin δ d ((sectionLin δ e) z - z) + sectionLin δ d z := by
              rw [map_sub, sub_add_cancel]
        _ = ((sectionLin δ e) z - z) + sectionLin δ d z := by rw [h1]
        _ = ((sectionLin δ d) z - z) + sectionLin δ e z := by abel
        _ = sectionLin δ e ((sectionLin δ d) z - z) + sectionLin δ e z := by rw [h2]
        _ = sectionLin δ e ((sectionLin δ d) z) := by rw [map_sub, sub_add_cancel]
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
      apply Subtype.ext
      simpa [pow_two] using hA2 x.1 x.2
  have hquadA : ∀ a ∈ sectionSub δ, ∀ b ∈ sectionSub δ, ∀ w,
      b (a w - w) = a w - w := by
    rintro a ⟨d, rfl⟩ b ⟨e, rfl⟩ w
    simpa [sectionLin_apply] using hquad d e w
  have hoffA : Nat.card Z ≤ Nat.card (sectionSub δ) * Nat.card (fixGL (sectionSub δ)) := by
    have h := offender_image δ hoff
    have hcard : Nat.card (sectionSub δ) = Nat.card δ.toHomUnits.range := by
      rw [sectionSub, sectionLin, MonoidHom.range_comp]
      exact Subgroup.card_map_of_injective (glEquiv Z).injective
    have hfix : Nat.card (fixGL (sectionSub δ)) =
        Nat.card {w : Z // ∀ a ∈ δ.toHomUnits.range, a.val w = w} := by
      apply Nat.card_congr
      refine Equiv.subtypeEquivRight fun w => ?_
      constructor
      · intro hw a ha
        obtain ⟨d, rfl⟩ := ha
        have h := hw (sectionLin δ d) ⟨d, rfl⟩
        simpa [sectionLin_apply, MonoidHom.coe_toHomUnits] using h
      · rintro hw s ⟨d, rfl⟩
        have h := hw (δ.toHomUnits d) ⟨d, rfl⟩
        simpa [sectionLin_apply, MonoidHom.coe_toHomUnits] using h
    rw [hcard, hfix]
    exact h
  have : CFSG.IsElementaryAbelian 2 (sectionSub δ) := hAel
  exact no_transitive_perfect_orbit_k (k := ZMod 2) (W := Z) (s := 2) (by norm_num)
    (factorSub ρ) hcomm hLperf hLnt hirr (sectionSub δ) hquadA hoffA hperm htrans

end CFSG.LieType.SpecialLinear
