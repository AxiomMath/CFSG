module

public import CFSG.LocalAnalysis.SteinbergBVSp6LayerStatements
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.KProperOddCoreFreeLayer
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBU

open Subgroup

theorem pPrimeCore_two_quotient_eq_map {F : Type*} [Group F] [Finite F] (N : Subgroup F)
    [N.Normal] (hN : N ≤ CFSG.pPrimeCore 2 F) :
    CFSG.pPrimeCore 2 (F ⧸ N) = (CFSG.pPrimeCore 2 F).map (QuotientGroup.mk' N) := by
  have hNodd : Nat.Coprime 2 (Nat.card N) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hN) CFSG.pPrimeCore_coprime_card
  apply le_antisymm
  · set P := CFSG.pPrimeCore 2 (F ⧸ N)
    have hker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
    have hNP : N ≤ P.comap (QuotientGroup.mk' N) := by
      intro x hx
      rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem P
    have hrel := Subgroup.relIndex_ker (P.comap (QuotientGroup.mk' N)) (QuotientGroup.mk' N)
    rw [hker, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)] at hrel
    have hcard : Nat.card (P.comap (QuotientGroup.mk' N)) = Nat.card P * Nat.card N := by
      rw [← Subgroup.relIndex_mul_card N (P.comap (QuotientGroup.mk' N)), inf_of_le_left hNP,
        hrel]
    have hle : P.comap (QuotientGroup.mk' N) ≤ CFSG.pPrimeCore 2 F := by
      refine le_sSup ⟨CFSG.pPrimeCore_normal.comap _, ?_⟩
      rw [hcard]
      exact Nat.Coprime.mul_right CFSG.pPrimeCore_coprime_card hNodd
    calc P = (P.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) :=
          (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) P).symm
      _ ≤ _ := Subgroup.map_mono hle
  · exact le_sSup ⟨CFSG.pPrimeCore_normal.map _ (QuotientGroup.mk'_surjective N),
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) CFSG.pPrimeCore_coprime_card⟩

theorem exists_mul_ne_mul_GL_three_two : ∃ x y : GL (Fin 3) (ZMod 2), x * y ≠ y * x := by
  by_contra h
  push Not at h
  have hZ : center (GL (Fin 3) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨c, rfl⟩
    rw [mem_bot, Subsingleton.elim c 1, map_one]
  have htop : center (GL (Fin 3) (ZMod 2)) = ⊤ :=
    eq_top_iff.2 fun x _ => mem_center_iff.2 fun y => h y x
  have h1 : Nat.card (GL (Fin 3) (ZMod 2)) = 1 := by
    rw [← card_top (G := GL (Fin 3) (ZMod 2)), ← htop, hZ, card_bot]
  rw [BinarySymplecticSix.FusionOrbits.card_GL_three_two] at h1
  exact absurd h1 (by norm_num)

@[expose] def firstRowUnipotent (x y : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, x, y; 0, 1, 0; 0, 0, 1]

theorem firstRowUnipotent_mul (x y x' y' : ZMod 2) :
    firstRowUnipotent x y * firstRowUnipotent x' y' = firstRowUnipotent (x + x') (y + y') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstRowUnipotent, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem firstRowUnipotent_self_mul (x y : ZMod 2) :
    firstRowUnipotent x y * firstRowUnipotent x y = 1 := by
  rw [firstRowUnipotent_mul]
  have h : ∀ t : ZMod 2, t + t = 0 := by decide
  rw [h, h]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def firstRowHom : Multiplicative (ZMod 2 × ZMod 2) →* GL (Fin 3) (ZMod 2) where
  toFun p := ⟨firstRowUnipotent p.toAdd.1 p.toAdd.2, firstRowUnipotent p.toAdd.1 p.toAdd.2,
    firstRowUnipotent_self_mul _ _, firstRowUnipotent_self_mul _ _⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' p q := by
    ext i j
    simp only [Units.val_mul, firstRowUnipotent_mul]
    rfl

theorem firstRowHom_injective : Function.Injective firstRowHom := by
  intro p q h
  have h1 := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1) h
  have h2 := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2) h
  simp only [firstRowHom, MonoidHom.coe_mk, OneHom.coe_mk, firstRowUnipotent] at h1 h2
  exact Multiplicative.toAdd.injective (Prod.ext (by simpa using h1) (by simpa using h2))

theorem exists_four_subgroup_of_injective {F : Type*} [Group F]
    {ι : GL (Fin 3) (ZMod 2) →* F} (hι : Function.Injective ι) :
    ∃ E : Subgroup F, E ≤ ι.range ∧ CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  let f := ι.comp firstRowHom
  have hf : Function.Injective f := hι.comp firstRowHom_injective
  refine ⟨f.range, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨firstRowHom x, rfl⟩
  · have hcomm : ∀ x y : Multiplicative (ZMod 2 × ZMod 2), x * y = y * x := mul_comm
    have hp : ∀ x : Multiplicative (ZMod 2 × ZMod 2), x ^ 2 = 1 := by decide
    exact
      { is_comm := ⟨fun a b => by
          obtain ⟨x, hx⟩ := a.2
          obtain ⟨y, hy⟩ := b.2
          apply Subtype.ext
          change (a : F) * b = b * a
          rw [← hx, ← hy, ← map_mul, ← map_mul, hcomm]⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
          obtain ⟨x, hx⟩ := a.2
          apply Subtype.ext
          change (a : F) ^ 2 = 1
          rw [← hx, ← map_pow, hp, map_one] }
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_eq_fintype_card]
    rfl

theorem exists_prod_equiv_of_diag {H M : Type*} [Group H] [Group M] {J D : Subgroup H} {a : H}
    (f : M → H) (κ : M ≃* J) (hκ : ∀ m, (κ m : H) = f m)
    (h : ∃ ψ : D ≃* J × J,
      (∀ (j : H) (hjJ : j ∈ J) (hjD : j ∈ D), ψ ⟨j, hjD⟩ = (⟨j, hjJ⟩, ⟨j, hjJ⟩)) ∧
      ∀ (d : H) (hd : d ∈ D) (hda : a⁻¹ * d * a ∈ D),
        ψ ⟨a⁻¹ * d * a, hda⟩ = (ψ ⟨d, hd⟩).swap) :
    ∃ Ψ : D ≃* M × M, (∀ (m : M) (h : f m ∈ D), Ψ ⟨f m, h⟩ = (m, m)) ∧
      ∀ (d : H) (hd : d ∈ D) (hda : a⁻¹ * d * a ∈ D),
        Ψ ⟨a⁻¹ * d * a, hda⟩ = (Ψ ⟨d, hd⟩).swap := by
  obtain ⟨ψ, hdiag, hswap⟩ := h
  refine ⟨ψ.trans (κ.symm.prodCongr κ.symm), fun m hm => ?_, fun d hd hda => ?_⟩
  · have hmJ : f m ∈ J := hκ m ▸ (κ m).2
    have hk : (⟨f m, hmJ⟩ : J) = κ m := Subtype.ext (hκ m).symm
    change (κ.symm (ψ ⟨f m, hm⟩).1, κ.symm (ψ ⟨f m, hm⟩).2) = (m, m)
    rw [hdiag (f m) hmJ hm, hk, MulEquiv.symm_apply_apply]
  · change (κ.symm (ψ ⟨_, hda⟩).1, κ.symm (ψ ⟨_, hda⟩).2) =
      (κ.symm (ψ ⟨d, hd⟩).2, κ.symm (ψ ⟨d, hd⟩).1)
    rw [hswap d hd hda]
    rfl

theorem exists_diag_equiv_of_prod {H M : Type*} [Group H] [Group M] {J D : Subgroup H} {a : H}
    (f : M → H) (κ : M ≃* J) (hκ : ∀ m, (κ m : H) = f m)
    (h : ∃ Ψ : D ≃* M × M, (∀ (m : M) (h : f m ∈ D), Ψ ⟨f m, h⟩ = (m, m)) ∧
      ∀ (d : H) (hd : d ∈ D) (hda : a⁻¹ * d * a ∈ D),
        Ψ ⟨a⁻¹ * d * a, hda⟩ = (Ψ ⟨d, hd⟩).swap) :
    ∃ ψ : D ≃* J × J,
      (∀ (j : H) (hjJ : j ∈ J) (hjD : j ∈ D), ψ ⟨j, hjD⟩ = (⟨j, hjJ⟩, ⟨j, hjJ⟩)) ∧
      ∀ (d : H) (hd : d ∈ D) (hda : a⁻¹ * d * a ∈ D),
        ψ ⟨a⁻¹ * d * a, hda⟩ = (ψ ⟨d, hd⟩).swap := by
  obtain ⟨Ψ, hdiag, hswap⟩ := h
  refine ⟨Ψ.trans (κ.prodCongr κ), fun j hjJ hjD => ?_, fun d hd hda => ?_⟩
  · have hm : f (κ.symm ⟨j, hjJ⟩) = j := by
      rw [← hκ, MulEquiv.apply_symm_apply]
    have hD' : f (κ.symm ⟨j, hjJ⟩) ∈ D := by
      rw [hm]
      exact hjD
    have hjm : (⟨j, hjD⟩ : D) = ⟨f (κ.symm ⟨j, hjJ⟩), hD'⟩ := Subtype.ext hm.symm
    change (κ (Ψ ⟨j, hjD⟩).1, κ (Ψ ⟨j, hjD⟩).2) = _
    rw [hjm, hdiag _ hD', MulEquiv.apply_symm_apply]
  · change (κ (Ψ ⟨_, hda⟩).1, κ (Ψ ⟨_, hda⟩).2) = (κ (Ψ ⟨d, hd⟩).2, κ (Ψ ⟨d, hd⟩).1)
    rw [hswap d hd hda]
    rfl

theorem eq_or_eq_of_isComponent_of_centralizer_eq_bot {H : Type*} [Group H] [Finite H]
    {D D₁ D₂ K : Subgroup H} (h₁ : CFSG.IsComponent D₁) (h₂ : CFSG.IsComponent D₂)
    (hsup : D₁ ⊔ D₂ = D) (hC : centralizer (D : Set H) = ⊥) (hK : CFSG.IsComponent K) :
    K = D₁ ∨ K = D₂ := by
  rcases CFSG.LocalCores.distinct_components_commute hK h₁ with h | h₁'
  · exact Or.inl h
  rcases CFSG.LocalCores.distinct_components_commute hK h₂ with h | h₂'
  · exact Or.inr h
  exfalso
  have hle : K ≤ centralizer (D : Set H) := by
    rw [le_centralizer_iff, ← hsup, sup_le_iff, ← commutator_eq_bot_iff_le_centralizer,
      ← commutator_eq_bot_iff_le_centralizer]
    exact ⟨(commutator_comm _ _).trans h₁', (commutator_comm _ _).trans h₂'⟩
  rw [hC, le_bot_iff] at hle
  obtain ⟨-, -, a, b, hab⟩ := hK.1
  apply hab
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  have hx : x = 1 := Subtype.ext (mem_bot.mp (hle ▸ x.2))
  have hy : y = 1 := Subtype.ext (mem_bot.mp (hle ▸ y.2))
  rw [hx, hy]

theorem xor_layer_alternatives_of {H M : Type*} [Group H] [Finite H] [Group M]
    {J D : Subgroup H} {a : H} (f : M → H) (κ : M ≃* J) (hκ : ∀ m, (κ m : H) = f m)
    (hC : centralizer (D : Set H) = ⊥) (h : SteinbergBV.OneOrTwoLayerAlternatives J D a) :
    Xor (IsSimpleGroup D ∧ (∃ x y : D, x * y ≠ y * x) ∧ J < D ∧ ∃ d ∈ D, a⁻¹ * d * a ≠ d)
      (∃ D₁ D₂ : Subgroup H, CFSG.IsComponent D₁ ∧ CFSG.IsComponent D₂ ∧ D₁ ≠ D₂ ∧
        IsSimpleGroup D₁ ∧ (∃ x y : D₁, x * y ≠ y * x) ∧
        IsSimpleGroup D₂ ∧ (∃ x y : D₂, x * y ≠ y * x) ∧
        D₁ ⊔ D₂ = D ∧ D₁ ⊓ D₂ = ⊥ ∧ ⁅D₁, D₂⁆ = ⊥ ∧
        D₁.map (MulAut.conj a⁻¹).toMonoidHom = D₂ ∧ J = D ⊓ centralizer {a} ∧
        (∀ K : Subgroup H, CFSG.IsComponent K → K = D₁ ∨ K = D₂) ∧
        ∃ Ψ : D ≃* M × M, (∀ (m : M) (h : f m ∈ D), Ψ ⟨f m, h⟩ = (m, m)) ∧
          ∀ (d : H) (hd : d ∈ D) (hda : a⁻¹ * d * a ∈ D),
            Ψ ⟨a⁻¹ * d * a, hda⟩ = (Ψ ⟨d, hd⟩).swap) := by
  rcases h with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · refine Or.inl ⟨hA, ?_⟩
    rintro ⟨D₁, D₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, hΨ⟩
    exact hB ⟨D₁, D₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      exists_diag_equiv_of_prod f κ hκ hΨ⟩
  · refine Or.inr ⟨?_, hA⟩
    obtain ⟨D₁, D₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hψ⟩ := hB
    exact ⟨D₁, D₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      fun K hK => eq_or_eq_of_isComponent_of_centralizer_eq_bot h1 h2 h8 hC hK,
      exists_prod_equiv_of_diag f κ hκ hψ⟩

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBU
