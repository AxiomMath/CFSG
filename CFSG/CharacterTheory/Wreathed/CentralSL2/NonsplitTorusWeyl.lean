module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.NonsplitCharacters

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

theorem two_ne_zero_of_not_isSquare {F : Type} [Field F] [Finite F] {b : Fˣ}
    (hb : ¬ IsSquare b) : (2 : F) ≠ 0 := by
  apply Ring.two_ne_zero
  intro hc
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hc (b : F)
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  exact hb ⟨Units.mk0 s hs0, Units.ext (by simpa using hs)⟩

theorem cyclicGenerator_pow_m_mem_nonsplitTorus {F : Type} [Field F] [Fintype F] {b : Fˣ}
    {m : ℕ} {hm : 0 < m} {heven : Even m} {E : Type} [Field E] [Algebra F E]
    {basis : Module.Basis (Fin 2) F E} (h2 : (2 : F) ≠ 0) :
    cyclicGenerator F b m hm heven ^ m ∈ nonsplitTorus F b m hm heven E basis := by
  rw [← nonsplitDiag_negOneE (hm := hm) (heven := heven) (basis := basis) h2]
  exact nonsplitDiag_mem _

theorem base_nonsplit_torus_and_weyl_action {F : Type} [Field F] [Fintype F]
    {p f : ℕ} (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hcard : Nat.card F = p ^ f)
    (b : Fˣ) (hb : ¬ IsSquare b) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (E : Type) [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E)
    (z y : Eˣ) (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) :
    let h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
    let G := CentralExtension F b m hm heven
    let u := cyclicGenerator F b m hm heven
    let a := u ^ 2
    let x := u ^ m
    let A := Subgroup.zpowers a
    let q := Nat.card F
    let C : E → Matrix (Fin 2) (Fin 2) F := fun t => Algebra.leftMulMatrix basis t
    let S₀ := LinearMap.toMatrix basis basis (FiniteField.frobeniusAlgHom F E).toLinearMap
    let J := nonsquareMatrix F b
    let hminus := nonsplitDiag F b m hm heven E basis
    let vminus := nonsplitGenerator F b m hm heven E basis z hz
    let wminus := nonsplitWeyl F b m hm heven E basis h2 y hy
    let r := rE F E b h2 z hz
    let β := βE F E basis z
    let cminus := cMinus F E b m h2 z hz
    let κ := projectiveMap F b m hm heven
    let T := nonsplitTorus F b m hm heven E basis
    let lam := nonsplitCharacter F b m hm heven E basis h2 z hz
    let weylP := nonsplitWeylParameter F b m heven E basis h2 z hz
    (∀ t : E, FiniteField.frobeniusAlgHom F E t = t ^ q) ∧
    (∀ t : Eˣ, t ∈ normOne F E ↔ (t : E) * (t : E) ^ q = 1) ∧
    (∃ z' : Eˣ, (z' : E) * (z' : E) ^ q = algebraMap F E b) ∧
    (∃ y' : Eˣ, (y' : E) * (y' : E) ^ q = -1) ∧
    IsCyclic (normOne F E) ∧ Nat.card (normOne F E) = q + 1 ∧
    (∀ t : normOne F E, ((mulSL F E basis t : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = C ((t : Eˣ) : E) ∧
      hminus t = specialInclusion F b m hm heven (mulSL F E basis t)) ∧
    ((vMatrix F E basis b z hz : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      C z * ((J⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∧
    (C z * ((J⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).det = 1 ∧
    vminus = specialInclusion F b m hm heven (vMatrix F E basis b z hz) * u ∧
    ((wMatrix F E basis h2 y hy : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = C y * S₀ ∧ (C y * S₀).det = 1 ∧
    wminus = specialInclusion F b m hm heven (wMatrix F E basis h2 y hy) ∧
    (((r : normOne F E) : Eˣ) : E) = -((z : E) ^ 2) / algebraMap F E b ∧
    (((β : normOne F E) : Eˣ) : E) = (z : E) ^ q / z ∧
    (((negOneE F E h2 : normOne F E) : Eˣ) : E) = -1 ∧ cminus = negOneE F E h2 * r ^ (m / 2) ∧
    (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)),
      κ (quotientClass F b m hm heven X j) =
        ProjGenLinGroup.mk (SpecialLinearGroup.toGL X * J ^ j.val)) ∧
    (∀ s : Eˣ, ((mulGL F E basis s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = C s) ∧
    (∀ g : G, g ∈ T ↔ ∃ s : Eˣ, ProjGenLinGroup.mk (mulGL F E basis s) = κ g) ∧
    Function.Surjective κ ∧ κ.ker = A ∧ Nat.card A = m ∧
    (∀ g ∈ T, ∀ g' ∈ T, g * g' = g' * g) ∧ Nat.card T = m * (q + 1) ∧
    Function.Injective hminus ∧ T = Subgroup.closure (Set.range hminus ∪ {vminus}) ∧
    (∀ t : normOne F E, vminus * hminus t = hminus t * vminus) ∧
    vminus ^ 2 = hminus r * a ∧ vminus ^ m = hminus cminus ∧
    (∀ (K : Type) [Group K] (η : normOne F E →* K) (ζ : K), (∀ t, ζ * η t = η t * ζ) →
      ζ ^ m = η cminus →
      ∃! φ : T →* K, (∀ t, φ ⟨hminus t, nonsplitDiag_mem t⟩ = η t) ∧
        φ ⟨vminus, nonsplitGenerator_mem z hz⟩ = ζ) ∧
    (∀ g ∈ T, ∃! tk : normOne F E × Fin m, g = hminus tk.1 * vminus ^ (tk.2 : ℕ)) ∧
    β = negOneE F E h2 * r⁻¹ ∧ ¬ IsSquare β ∧
    wminus ^ 2 = x ∧ (∀ t : normOne F E, wminus * hminus t * wminus⁻¹ = hminus t⁻¹) ∧
    wminus * vminus * wminus⁻¹ = a * x * vminus⁻¹ ∧
    A ≤ T ∧ (∀ g ∈ T, wminus * g * wminus⁻¹ = g ↔ g ∈ A) ∧
    (∀ (ν : normOne F E →* ℂˣ) (ζ : ℂˣ), ζ ^ m = ν cminus →
      ∃! φ : T →* ℂˣ, (∀ t, φ ⟨hminus t, nonsplitDiag_mem t⟩ = ν t) ∧
        φ ⟨vminus, nonsplitGenerator_mem z hz⟩ = ζ) ∧
    (∀ P : NonsplitParameter F E b m h2 z hz,
      (∀ t, lam P ⟨hminus t, nonsplitDiag_mem t⟩ = P.1.1 t) ∧
        lam P ⟨vminus, nonsplitGenerator_mem z hz⟩ = P.1.2) ∧
    Function.Bijective lam ∧ Nat.card (T →* ℂˣ) = m * (q + 1) ∧
    (∀ g : T, (nonsplitWeylConj F b m hm heven E basis h2 z hz y hy g : G) =
      wminus⁻¹ * g * wminus) ∧
    (∀ P, (weylP P).1 = (P.1.1⁻¹, P.1.1 β * P.1.2)) ∧
    (∀ P, (lam P).comp (nonsplitWeylConj F b m hm heven E basis h2 z hz y hy) = lam (weylP P)) ∧
    Function.Involutive weylP ∧ (∀ P, weylP P = P ↔ P.1.1 = 1) ∧
    Set.ncard {P : NonsplitParameter F E b m h2 z hz | P.1.1 ≠ 1} = m * q ∧
    Set.ncard ((fun P => ({P, weylP P} : Set (NonsplitParameter F E b m h2 z hz))) ''
      {P : NonsplitParameter F E b m h2 z hz | P.1.1 ≠ 1}) = m * q / 2 ∧
    (∀ P, lam P ⟨x, cyclicGenerator_pow_m_mem_nonsplitTorus h2⟩ = P.1.1 (negOneE F E h2)) := by
  intro h2 G u a x A q C S₀ J hminus vminus wminus r β cminus κ T lam weylP
  have := finite_of_basis F E basis
  have hfin : Finite F := inferInstance
  refine ⟨frobeniusAlgHom_apply' F E, mem_normOne_iff F E, exists_norm_eq F E basis b,
    exists_norm_eq F E basis (-1) |>.imp fun y' hy' => by rw [hy']; simp,
    normOne_isCyclic F E, card_normOne F E basis, fun t => ⟨rfl, rfl⟩, rfl, ?_, rfl, rfl, ?_,
    rfl, rE_val F E b h2 z hz, βE_val F E basis z, ?_, rfl,
    projectiveMap_quotientClass F b m hm heven, fun s => rfl, mem_nonsplitTorus_iff,
    projectiveMap_surjective F b m hm heven hb, projectiveMap_ker F b m hm heven hb, ?_,
    fun g hg g' hg' => nonsplitTorus_mul_comm z hz hg hg', card_nonsplitTorus z hz,
    nonsplitDiag_injective, nonsplitTorus_eq_closure z hz,
    nonsplitGenerator_mul_nonsplitDiag z hz, nonsplitGenerator_sq z hz h2,
    nonsplitGenerator_pow_m z hz h2, fun K _ η ζ hc hζ => nonsplitTorus_lift z hz h2 η ζ hc hζ,
    ?_, βE_eq F E basis b h2 z hz, βE_not_isSquare F E basis b h2 hb z hz,
    nonsplitWeyl_sq y hy h2, nonsplitWeyl_conj_nonsplitDiag y hy h2,
    nonsplitWeyl_conj_nonsplitGenerator z hz y hy h2, zpowers_le_nonsplitTorus hb,
    fun g hg => nonsplitTorus_fixed_iff z hz y hy h2 hb hg,
    fun ν ζ hζ => nonsplitTorus_lift z hz h2 ν ζ (fun _ => mul_comm _ _) hζ,
    nonsplitCharacter_spec F b m hm heven E basis h2 z hz,
    (nonsplitCharacterEquiv F b m hm heven E basis h2 z hz).bijective,
    card_nonsplitTorus_characters F b m hm heven E basis h2 z hz,
    nonsplitWeylConj_apply F b m hm heven E basis h2 z hz y hy,
    nonsplitWeylParameter_fst F b m heven E basis h2 z hz,
    nonsplitCharacter_comp_weylConj F b m hm heven E basis h2 z hz y hy,
    nonsplitWeylParameter_involutive F b m heven E basis h2 z hz,
    nonsplitWeylParameter_eq_self_iff F b m heven E basis h2 z hz hb,
    (nonsplitParameter_orbits F b m hm heven E basis h2 z hz hb).1,
    (nonsplitParameter_orbits F b m hm heven E basis h2 z hz hb).2,
    fun P => nonsplitCharacter_x F b m hm heven E basis h2 z hz P _⟩
  · exact (vMatrix F E basis b z hz).2
  · exact (wMatrix F E basis h2 y hy).2
  · simp [negOneE]
  · rw [Nat.card_zpowers, orderOf_cyclicGenerator_sq F b m hm heven h2]
  · intro g hg
    obtain ⟨t, k, hk⟩ := nonsplitTorus_normalForm z hz g hg
    refine ⟨(t, k), hk, ?_⟩
    rintro ⟨t', k'⟩ hk'
    obtain ⟨h1, h3⟩ := nonsplitTorus_normalForm_unique z hz (hk'.symm.trans hk)
    exact Prod.ext h1 h3

end CFSG.Wreathed.CentralSL2
