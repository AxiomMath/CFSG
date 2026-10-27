module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Pair
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Fam

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Classical CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Order

theorem mem_of_pow_five_mem {M : Type*} [Group M] {x : M} (hx : Nat.Coprime 5 (orderOf x))
    {P : Subgroup M} (h : x ^ 5 ∈ P) : x ∈ P := by
  rcases Nat.eq_zero_or_pos (orderOf x) with h0 | hpos
  · rw [h0] at hx
    norm_num at hx
  by_cases h1 : orderOf x = 1
  · rw [orderOf_eq_one_iff.1 h1]
    exact one_mem _
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hx (by omega)
  have e : x = (x ^ 5) ^ m := by
    rw [← pow_mul, ← pow_mod_orderOf, hm, pow_one]
  rw [e]
  exact pow_mem h m

theorem coprime_orderOf_of_mem_core {G : Type*} [Group G] [Finite G] {C : Subgroup G} {o : G}
    (ho : o ∈ GLAPPrimeCoreOf 5 C) : Nat.Coprime 5 (orderOf o) := by
  have hcop := coprime_card_gLAPPrimeCoreOf' (p := 5) Nat.prime_five C
  have h1 : orderOf (⟨o, ho⟩ : GLAPPrimeCoreOf 5 C) ∣ Nat.card (GLAPPrimeCoreOf 5 C) :=
    orderOf_dvd_natCard _
  have h2 : orderOf o = orderOf (⟨o, ho⟩ : GLAPPrimeCoreOf 5 C) :=
    Subgroup.orderOf_coe (⟨o, ho⟩ : GLAPPrimeCoreOf 5 C)
  rw [h2]
  exact hcop.coprime_dvd_right h1

theorem eq_one_of_pow_five_of_mem_core {G : Type*} [Group G] [Finite G] {C : Subgroup G} {o : G}
    (ho : o ∈ GLAPPrimeCoreOf 5 C) (h5 : o ^ 5 = 1) : o = 1 := by
  have h1 := coprime_orderOf_of_mem_core ho
  have h2 : orderOf o ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have : orderOf o = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h1) h2
  exact orderOf_eq_one_iff.1 this

end Order

section Leaf

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

noncomputable abbrev Wm (L : Type) [Field L] [CharP L 2] :
    Subgroup (ModGL Tag.E8 L) :=
  twModel (canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl) (iterateFrobenius L 2 1)

theorem five_of_orderOf {ζ : Lˣ} (hζ : orderOf ζ = 5) : ζ ^ 5 = 1 := by
  rw [← hζ]
  exact pow_orderOf_eq_one ζ

@[expose] noncomputable def phiW (ζ : Lˣ) (hζ : orderOf ζ = 5) :
    Multiplicative (Fin 4 → ZMod 5) →* Wm L :=
  (phi5 ζ (five_of_orderOf hζ)).codRestrict (Wm L) fun c =>
    phi5_mem_twModel hζ iterateFrobenius_two_one (Multiplicative.toAdd c)

theorem phiW_injective {ζ : Lˣ} (hζ : orderOf ζ = 5) : Function.Injective (phiW (L := L) ζ hζ) := by
  intro a b h
  apply phi5_injective hζ (five_of_orderOf hζ)
  exact congrArg Subtype.val h

@[expose] noncomputable def famC (ζ : Lˣ) (hζ : orderOf ζ = 5) (f : Fin 4 → ZMod 5) :
    Subgroup (Wm L) :=
  Subgroup.centralizer (phiAdd (phiW (L := L) ζ hζ) '' {c | f ⬝ᵥ c = 0})

theorem mem_familyCentralizer_of_mem_famC {ζ : Lˣ} (hζ : orderOf ζ = 5) {f : Fin 4 → ZMod 5}
    {g : Wm L} (hg : g ∈ famC ζ hζ f) :
    (g : ModGL Tag.E8 L) ∈ familyCentralizer Tag.E8 L (famPar ζ f) := by
  rw [mem_familyCentralizer]
  refine ⟨g.2.1, fun c => ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.1 hg (phiAdd (phiW (L := L) ζ hζ) c.1) ⟨c.1, c.2, rfl⟩
  have h2 : d5 ζ (xc c.1) * (g : ModGL Tag.E8 L) = (g : ModGL Tag.E8 L) * d5 ζ (xc c.1) :=
    congrArg Subtype.val h1
  change d5 ζ (xc c.1) * (g : ModGL Tag.E8 L) * (d5 ζ (xc c.1))⁻¹ = g
  rw [h2, mul_assoc, mul_inv_cancel, mul_one]

theorem leaf_core_eq_bot_D1 {ζ : Lˣ} (hζ : orderOf ζ = 5) [Finite (Wm L)]
    {f : Fin 4 → ZMod 5} (hD1 : LeafD1 (famPar ζ f)) :
    GLAPPrimeCoreOf 5 (famC ζ hζ f) = ⊥ := by
  refine eq_bot_iff.2 fun o ho => ?_
  rw [Subgroup.mem_bot]
  have hoC : o ∈ famC ζ hζ f := gLAPPrimeCoreOf_le_self' _ ho
  obtain ⟨u, hu, m, hm, he⟩ := familyCentralizer_le_mul Tag.E8 L (famPar ζ f)
    (mem_familyCentralizer_of_mem_famC hζ hoC)
  rw [hD1.2 u hu, canonicalRep_one, mul_one] at he
  have hmT : m ∈ torusGroup Tag.E8 L := by
    have hm' : m ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (familyKernel (famPar ζ f)) := hm
    rw [hD1.1] at hm'
    have hbot : rootSpan Tag.E8 L (∅ : Set (Fin Tag.E8.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    rwa [hbot, sup_bot_eq] at hm'
  have h5o : (o : ModGL Tag.E8 L) ^ 5 = 1 :=
    pow_five_of_mem_twModel_torus hζ iterateFrobenius_two_one o.2 (by rw [he]; exact hmT)
  exact eq_one_of_pow_five_of_mem_core ho (Subtype.ext (by simpa using h5o))

theorem leaf_core_eq_bot_D2_aux {ζ : Lˣ} (hζ : orderOf ζ = 5) [Finite (Wm L)]
    {f : Fin 4 → ZMod 5} {K₂ : Type} [Field K₂] [Finite K₂] [Algebra K₂ L]
    (hK4 : Nat.card K₂ = 4) (hK : ∀ c : L, c ∈ Set.range (algebraMap K₂ L) ↔ c ^ 4 = c)
    {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    (hker : familyKernel (famPar ζ f) = {α, -α, e8PhiFourWeyl • α, -(e8PhiFourWeyl • α)})
    (hstab : ∀ u ∈ familyStabilizer (famPar ζ f), u = 1 ∨ u = rootReflection α ∨
      u = rootReflection (e8PhiFourWeyl • α) ∨
      u = rootReflection α * rootReflection (e8PhiFourWeyl • α)) :
    GLAPPrimeCoreOf 5 (famC ζ hζ f) = ⊥ := by
  have hβ : IsRoot Tag.E8 (e8PhiFourWeyl • α) := (isRoot_smul_iff _).2 hα
  have h5 := five_of_orderOf hζ
  have hζ1 : ζ ≠ 1 := fun h => by rw [h, orderOf_one] at hζ; norm_num at hζ
  have hchar : CharP K₂ 2 := RingHom.charP (algebraMap K₂ L) (algebraMap K₂ L).injective 2
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K₂) :=
    haveI := hchar
    isSimpleGroup_SL2_charTwo (by rw [hK4])
  set C := famC ζ hζ f with hC
  set O := GLAPPrimeCoreOf 5 C with hO
  have hFam : familyGroup (famPar ζ f) = torusGroup Tag.E8 L ⊔ Lsp L α (e8PhiFourWeyl • α) := by
    rw [familyGroup, hker]
  have hOL : ∀ o ∈ O, (o : ModGL Tag.E8 L) ∈ Lsp L α (e8PhiFourWeyl • α) := by
    intro o ho
    have hoC : o ∈ C := gLAPPrimeCoreOf_le_self' C ho
    obtain ⟨u, hu, m, hm, he⟩ := familyCentralizer_le_mul Tag.E8 L (famPar ζ f)
      (mem_familyCentralizer_of_mem_famC hζ hoC)
    have hm' : m ∈ torusGroup Tag.E8 L ⊔ Lsp L α (e8PhiFourWeyl • α) := by
      rw [← hFam]
      exact hm
    have hnu := canonicalRep_mem_sup_Lsp (L := L) hα (hstab u hu)
    have hoM : (o : ModGL Tag.E8 L) ∈ torusGroup Tag.E8 L ⊔ Lsp L α (e8PhiFourWeyl • α) := by
      rw [he]
      exact mul_mem hm' hnu
    have hopow := pow_five_mem_Lsp hα o.2.2 hoM
    have hord : Nat.Coprime 5 (orderOf (o : ModGL Tag.E8 L)) := by
      rw [Subgroup.orderOf_coe]
      exact coprime_orderOf_of_mem_core ho
    exact mem_of_pow_five_mem hord hopow
  set P := Pmat h5 hζ1 with hP
  let ψ : Matrix.SpecialLinearGroup (Fin 2) K₂ →* ModGL Tag.E8 L :=
    (pairHom (iterateFrobenius L 2 1) α (e8PhiFourWeyl • α) (commute_rootSL2_pair hα) 1).comp
      ((conjSL P).comp (Matrix.SpecialLinearGroup.map (algebraMap K₂ L)))
  have hψapp : ∀ B, ψ B = pairElt (iterateFrobenius L 2 1) α (e8PhiFourWeyl • α) 1
      (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K₂ L) B)) := fun B => rfl
  have hψmemA : ∀ B, conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K₂ L) B) ∈
      (Matrix.SpecialLinearGroup.map (algebraMap K₂ L)).range.map (conjSL P) :=
    fun B => ⟨_, ⟨B, rfl⟩, rfl⟩
  have hψLsp : ∀ B, ψ B ∈ Lsp L α (e8PhiFourWeyl • α) := fun B => by
    rw [hψapp, pairElt, conjSL_diagUnitOne_one]
    exact mul_mem (rootSL2_mem_Lsp_left hα hβ _) (rootSL2_mem_Lsp_right hα hβ _)
  have hψadj : ∀ B, ψ B ∈ adjointGroup Tag.E8 L := fun B => by
    rw [hψapp, pairElt, conjSL_diagUnitOne_one]
    exact mul_mem (rootSL2_mem_adjointGroup _ _) (rootSL2_mem_adjointGroup _ _)
  have hψW : ∀ B, ψ B ∈ Wm L := fun B =>
    mem_twModel_iff_step.2 ⟨hψadj B, by
      rw [hψapp]
      exact stepHom_pairElt hα (swap_map_sq_conj' hK h5 hζ1 (hψmemA B))⟩
  let ψ' : Matrix.SpecialLinearGroup (Fin 2) K₂ →* Wm L := ψ.codRestrict (Wm L) hψW
  have hψ'C : ∀ B, ψ' B ∈ C := by
    intro B
    rw [hC, famC, Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    apply Subtype.ext
    have hfam : ψ B ∈ familyCentralizer Tag.E8 L (famPar ζ f) :=
      familyGroup_le_familyCentralizer _ (by rw [hFam]; exact Subgroup.mem_sup_right (hψLsp B))
    have h1 := (mem_familyCentralizer.1 hfam).2 ⟨c, hc⟩
    change rootDiagUnit Tag.E8 (torV5 ζ (xc c)) * ψ B *
      (rootDiagUnit Tag.E8 (torV5 ζ (xc c)))⁻¹ = ψ B at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hOψ : ∀ o ∈ O, ∃ B : Matrix.SpecialLinearGroup (Fin 2) K₂,
      (o : ModGL Tag.E8 L) = ψ B := by
    intro o ho
    obtain ⟨A, hA, he⟩ := fixed_of_mem_Lsp hα (hOL o ho) o.2.2
    obtain ⟨_, ⟨B, rfl⟩, hAB⟩ := mem_conj_range_of_swap_fixed hK h5 hζ1 hA
    exact ⟨B, by rw [he, hψapp, hAB]⟩
  let N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K₂) := O.comap ψ'
  have hNn : N.Normal := ⟨fun x hx g => by
    show ψ' (g * x * g⁻¹) ∈ O
    rw [map_mul, map_mul, map_inv]
    exact gLAPPrimeCoreOf_conj_mem' (ψ' g) (hψ'C g) (ψ' x) hx⟩
  haveI : N.Normal := hNn
  rcases hsimple.eq_bot_or_eq_top_of_normal N with hN0 | hN1
  · refine eq_bot_iff.2 fun o ho => ?_
    obtain ⟨B, hB⟩ := hOψ o ho
    have hBN : B ∈ N := by
      show ψ' B ∈ O
      have : ψ' B = o := Subtype.ext hB.symm
      rw [this]
      exact ho
    rw [hN0, Subgroup.mem_bot] at hBN
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [hB, hBN, map_one]
    rfl
  · exfalso
    obtain ⟨_, ⟨B₀, rfl⟩, hB₀⟩ := HSL_mem_conj_range hK h5 hζ1
    have hmem : ψ' B₀ ∈ O := by
      have : B₀ ∈ N := hN1 ▸ Subgroup.mem_top _
      exact this
    have hord5 : orderOf (ψ B₀) = 5 := by
      rw [hψapp, hB₀]
      exact orderOf_pairElt_HSL hα hβ (iform_smul_self_eq_zero e8PhiFourWeyl_sq_smul5 α)
        (commute_rootSL2_pair hα) _ 1 Nat.prime_five (by norm_num) hζ
    have h5card : 5 ∣ Nat.card O := by
      have h1 := orderOf_dvd_natCard (⟨ψ' B₀, hmem⟩ : O)
      have h2 : orderOf (⟨ψ' B₀, hmem⟩ : O) = 5 := by
        rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
        exact hord5
      rwa [h2] at h1
    have hcop := coprime_card_gLAPPrimeCoreOf' (p := 5) Nat.prime_five C
    exact absurd h5card ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hcop)

theorem leaf_core_eq_bot_D2 {ζ : Lˣ} (hζ : orderOf ζ = 5) [Finite (Wm L)] {f : Fin 4 → ZMod 5}
    (hD2 : LeafD2 (famPar ζ f)) : GLAPPrimeCoreOf 5 (famC ζ hζ f) = ⊥ := by
  obtain ⟨α, hα, hker, hstab⟩ := hD2
  obtain ⟨K₂, hF, hFin, hAlg, hK4, hK⟩ := exists_subfield_four (L := L)
  exact leaf_core_eq_bot_D2_aux (K₂ := K₂) hζ hK4 hK hα hker hstab

theorem leaf_core_eq_bot {ζ : Lˣ} (hζ : orderOf ζ = 5) [Finite (Wm L)] {f : Fin 4 → ZMod 5}
    (hN : NormF f) : GLAPPrimeCoreOf 5 (famC ζ hζ f) = ⊥ := by
  rcases leafData_of_normF hζ hN with hD1 | hD2
  · exact leaf_core_eq_bot_D1 hζ hD1
  · exact leaf_core_eq_bot_D2 hζ hD2

theorem gLAPPrimeCoreOf_centralizer_phiW {ζ : Lˣ} (hζ : orderOf ζ = 5) [Finite (Wm L)]
    {y : Fin 4 → ZMod 5} (hy : y ≠ 0) :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer {phiAdd (phiW (L := L) ζ hζ) y}) = ⊥ :=
  gLAPPrimeCoreOf_centralizer_of_hyperplanes (phiW ζ hζ) (phiW_injective hζ)
    (fun f hN => leaf_core_eq_bot hζ hN) hy

end Leaf

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end
