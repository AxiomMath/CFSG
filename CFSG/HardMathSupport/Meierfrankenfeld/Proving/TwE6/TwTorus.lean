module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Surv27
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverTwRank

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem exists_isSymU_of_mem_H {h : ↥(TwistedE6.fixedGroup K σ)}
    (hh : h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ)) :
    ∃ u : Fin (Tag.rank .E6) → Kˣ, TwistedE6.IsSymU σ u ∧
      minTorus e6Data_valid K u = (h : ↥(e6Data_valid.minGroup K)) := by
  have hT : ((Isogeny.e6IsogenyT K (h : ↥(e6Data_valid.minGroup K)) :
        ↥(adjointGroup TwistTag.E6.tag K)) : ModGL TwistTag.E6.tag K) ∈
        torusGroup TwistTag.E6.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1
      (show ((coverHom hf hK σ hσ h : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
        ModGL TwistTag.E6.tag K) ∈ graphFixedRootTorus TwistTag.E6 K σ from hh)).1).1
  have hH : (h : ↥(e6Data_valid.minGroup K)) ∈
      (chevDatumLD TwistTag.E6 K 2 e6LongestData).H.comap (Isogeny.e6IsogenyT K) :=
    Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 hT)
  obtain ⟨u, hu⟩ := e6_H_le_range_minTorus hH
  refine ⟨u, ?_, hu⟩
  have hfix : TwistedE6.sigma K σ (minTorus e6Data_valid K u) = minTorus e6Data_valid K u := by
    rw [hu]
    exact (TwistedE6.mem_fixedGroup σ).1 h.2
  rw [sigma_minTorus σ u] at hfix
  have hu' := minTorus_injective e6Data_valid K hfix
  intro a
  have := congrFun hu' (TwistedE6.rhoPerm a)
  rw [Equiv.symm_apply_apply] at this
  exact this.symm


theorem isSymU_pow {u : Fin (Tag.rank .E6) → Kˣ} (hu : TwistedE6.IsSymU σ u) (k : ℕ)
    (i : Fin (Tag.rank .E6)) :
    ((u ((TwistedE6.rhoPerm ^ k) i) : Kˣ) : K) = (σ ^ k) ((u i : Kˣ) : K) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, pow_succ', RingHom.mul_def,
      RingHom.comp_apply, ← ih]
    have := congrArg (fun v : Kˣ => (v : K)) (hu ((TwistedE6.rhoPerm ^ k) i))
    simpa using this

include hf hK hσ in
theorem hatH_val (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ) :
    ((hatH hf hK σ hσ a w : ↥(TwistedE6.fixedGroup K σ)) : ↥(e6Data_valid.minGroup K)) =
      minOrbitHom σ a (HSL w) := rfl

@[expose] def symUnit (u : Fin (Tag.rank .E6) → Kˣ) (a : Fin TwistTag.E6.foldedTag.rank)
    (hw : ((u (TwistTag.E6.orbitMin a) : Kˣ) : K) ∈ orbitField TwistTag.E6 K σ a) :
    (orbitField TwistTag.E6 K σ a)ˣ :=
  Units.mk0 (⟨((u (TwistTag.E6.orbitMin a) : Kˣ) : K), hw⟩ : orbitField TwistTag.E6 K σ a) (by
    intro h
    exact (u (TwistTag.E6.orbitMin a)).ne_zero (congrArg Subtype.val h))


include hf hK hσ in
theorem hatH_symUnit_eq {u : Fin (Tag.rank .E6) → Kˣ} (hu : TwistedE6.IsSymU σ u)
    (a : Fin TwistTag.E6.foldedTag.rank)
    (hw : ((u (TwistTag.E6.orbitMin a) : Kˣ) : K) ∈ orbitField TwistTag.E6 K σ a) :
    ((hatH hf hK σ hσ a (symUnit σ u a hw) : ↥(TwistedE6.fixedGroup K σ)) :
        ↥(e6Data_valid.minGroup K)) =
      minTorus e6Data_valid K (((List.range (TwistTag.E6.orbit a).card).map fun k =>
        (Pi.mulSingle ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a))
          (u ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a))) :
          Fin (Tag.rank .E6) → Kˣ)).prod) := by
  rw [hatH_val, minOrbitHom_HSL, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  refine Eq.trans ?_ (minTorus_mulSingle e6Data_valid K _ _).symm
  congr 1
  refine Units.ext ?_
  exact (isSymU_pow σ hu k _).symm


theorem perm_pow_card_orbitMin :
    ∀ a : Fin TwistTag.E6.foldedTag.rank,
      (TwistTag.E6.perm ^ (TwistTag.E6.orbit a).card) (TwistTag.E6.orbitMin a) =
        TwistTag.E6.orbitMin a := by
  decide

theorem mem_orbitField_of_isSymU {u : Fin (Tag.rank .E6) → Kˣ} (hu : TwistedE6.IsSymU σ u)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    ((u (TwistTag.E6.orbitMin a) : Kˣ) : K) ∈ orbitField TwistTag.E6 K σ a := by
  rw [mem_orbitField]
  have := isSymU_pow σ hu (TwistTag.E6.orbit a).card (TwistTag.E6.orbitMin a)
  have hp : (TwistedE6.rhoPerm ^ (TwistTag.E6.orbit a).card) (TwistTag.E6.orbitMin a) =
      TwistTag.E6.orbitMin a := perm_pow_card_orbitMin a
  rw [hp] at this
  exact this.symm

abbrev tw0 : Fin TwistTag.E6.foldedTag.rank := ⟨0, by decide⟩
abbrev tw1 : Fin TwistTag.E6.foldedTag.rank := ⟨1, by decide⟩
abbrev tw2 : Fin TwistTag.E6.foldedTag.rank := ⟨2, by decide⟩
abbrev tw3 : Fin TwistTag.E6.foldedTag.rank := ⟨3, by decide⟩

theorem eq_prod_mulSingle_six (u : Fin 6 → Kˣ) :
    u = (Pi.mulSingle 0 (u 0) * Pi.mulSingle 5 (u 5)) *
      (Pi.mulSingle 2 (u 2) * Pi.mulSingle 4 (u 4)) * Pi.mulSingle 3 (u 3) *
      Pi.mulSingle 1 (u 1) := by
  funext i
  fin_cases i <;> simp

include hf hK hσ in
theorem minTorus_eq_prod_hatH {u : Fin (Tag.rank .E6) → Kˣ} (hu : TwistedE6.IsSymU σ u) :
    minTorus e6Data_valid K u =
      ((hatH hf hK σ hσ tw0 (symUnit σ u tw0 (mem_orbitField_of_isSymU σ hu tw0)) :
          ↥(TwistedE6.fixedGroup K σ)) : ↥(e6Data_valid.minGroup K)) *
      ((hatH hf hK σ hσ tw1 (symUnit σ u tw1 (mem_orbitField_of_isSymU σ hu tw1)) :
          ↥(TwistedE6.fixedGroup K σ)) : ↥(e6Data_valid.minGroup K)) *
      ((hatH hf hK σ hσ tw2 (symUnit σ u tw2 (mem_orbitField_of_isSymU σ hu tw2)) :
          ↥(TwistedE6.fixedGroup K σ)) : ↥(e6Data_valid.minGroup K)) *
      ((hatH hf hK σ hσ tw3 (symUnit σ u tw3 (mem_orbitField_of_isSymU σ hu tw3)) :
          ↥(TwistedE6.fixedGroup K σ)) : ↥(e6Data_valid.minGroup K)) := by
  rw [hatH_symUnit_eq hf hK σ hσ hu tw0, hatH_symUnit_eq hf hK σ hσ hu tw1,
    hatH_symUnit_eq hf hK σ hσ hu tw2, hatH_symUnit_eq hf hK σ hσ hu tw3, ← map_mul, ← map_mul,
    ← map_mul]
  congr 1
  have c0 : (TwistTag.E6.orbit tw0).card = 2 := by decide
  have c1 : (TwistTag.E6.orbit tw1).card = 2 := by decide
  have c2 : (TwistTag.E6.orbit tw2).card = 1 := by decide
  have c3 : (TwistTag.E6.orbit tw3).card = 1 := by decide
  have m0 : TwistTag.E6.orbitMin tw0 = (⟨0, by decide⟩ : Fin 6) := Fin.ext (by decide)
  have m0' : TwistTag.E6.perm (TwistTag.E6.orbitMin tw0) = (⟨5, by decide⟩ : Fin 6) :=
    Fin.ext (by decide)
  have m1 : TwistTag.E6.orbitMin tw1 = (⟨2, by decide⟩ : Fin 6) := Fin.ext (by decide)
  have m1' : TwistTag.E6.perm (TwistTag.E6.orbitMin tw1) = (⟨4, by decide⟩ : Fin 6) :=
    Fin.ext (by decide)
  have m2 : TwistTag.E6.orbitMin tw2 = (⟨3, by decide⟩ : Fin 6) := Fin.ext (by decide)
  have m3 : TwistTag.E6.orbitMin tw3 = (⟨1, by decide⟩ : Fin 6) := Fin.ext (by decide)
  rw [c0, c1, c2, c3]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.singleton_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero, pow_one,
    Equiv.Perm.coe_one, id_eq]
  simp only [m0', m1']
  simp only [m0, m1, m2, m3]
  exact eq_prod_mulSingle_six u


section Chi

variable {k : Type} [Field k] [Algebra K k] [CharP k 2] {V W : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

include hf hK hσ in
theorem tw_chi_eq_on_H {ρ₁ : Representation k ↥(TwistedE6.fixedGroup K σ) V}
    {ρ₂ : Representation k ↥(TwistedE6.fixedGroup K σ) W} (hρ₁ : IsSimpleRep ρ₁)
    (hρ₂ : IsSimpleRep ρ₂) {y₁ : V} {y₂ : W} {χ₁ χ₂ : ↥(TwistedE6.fixedGroup K σ) → k}
    {J₁ J₂ : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht₁ : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ₁ y₁ χ₁ J₁)
    (ht₂ : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ₂ y₂ χ₂ J₂)
    (hd : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ₁ (hatH hf hK σ hσ a w) = χ₂ (hatH hf hK σ hσ a w)) :
    ∀ h ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ), χ₁ h = χ₂ h := by
  classical
  have hs := twistedCover_split hf hK σ hσ k
  obtain ⟨μ₁, hμ₁⟩ := ht₁.exists_mu hρ₁ hs
  obtain ⟨μ₂, hμ₂⟩ := ht₂.exists_mu hρ₂ hs
  intro h hh
  obtain ⟨u, hu, huh⟩ := exists_isSymU_of_mem_H hf hK σ hσ hh
  have hmem : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      hatH hf hK σ hσ a w ∈ (twistedE6Datum hf hK σ hσ).H.comap (coverHom hf hK σ hσ) :=
    fun a w => (twistedE6CoverRankOne hf hK σ hσ).hh_mem a w
  have hprod : h =
      hatH hf hK σ hσ tw0 (symUnit σ u tw0 (mem_orbitField_of_isSymU σ hu tw0)) *
      hatH hf hK σ hσ tw1 (symUnit σ u tw1 (mem_orbitField_of_isSymU σ hu tw1)) *
      hatH hf hK σ hσ tw2 (symUnit σ u tw2 (mem_orbitField_of_isSymU σ hu tw2)) *
      hatH hf hK σ hσ tw3 (symUnit σ u tw3 (mem_orbitField_of_isSymU σ hu tw3)) :=
    Subtype.ext (huh.symm.trans (minTorus_eq_prod_hatH hf hK σ hσ hu))
  have h0 := hmem tw0 (symUnit σ u tw0 (mem_orbitField_of_isSymU σ hu tw0))
  have h1 := hmem tw1 (symUnit σ u tw1 (mem_orbitField_of_isSymU σ hu tw1))
  have h2 := hmem tw2 (symUnit σ u tw2 (mem_orbitField_of_isSymU σ hu tw2))
  have h3 := hmem tw3 (symUnit σ u tw3 (mem_orbitField_of_isSymU σ hu tw3))
  rw [hprod, hμ₁.chi_mul (mul_mem (mul_mem h0 h1) h2) h3, hμ₁.chi_mul (mul_mem h0 h1) h2,
    hμ₁.chi_mul h0 h1, hμ₂.chi_mul (mul_mem (mul_mem h0 h1) h2) h3,
    hμ₂.chi_mul (mul_mem h0 h1) h2, hμ₂.chi_mul h0 h1, hd, hd, hd, hd]

end Chi

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.TwE6
