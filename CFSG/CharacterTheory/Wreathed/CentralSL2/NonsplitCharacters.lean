module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.NonsplitTorus
public import CFSG.CharacterTheory.Wreathed.CentralSL2.PrincipalSeries

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Counting

theorem card_hom_units_of_isCyclic (Γ : Type) [CommGroup Γ] [Finite Γ] [IsCyclic Γ] :
    Nat.card (Γ →* ℂˣ) = Nat.card Γ := by
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self Γ ℂ
  exact Nat.card_congr e.toEquiv

theorem finite_hom_units_of_isCyclic (Γ : Type) [CommGroup Γ] [Finite Γ] [IsCyclic Γ] :
    Finite (Γ →* ℂˣ) := by
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self Γ ℂ
  exact Finite.of_equiv _ e.toEquiv.symm

theorem card_parameter_of_isCyclic (Γ : Type) [CommGroup Γ] [Finite Γ] [IsCyclic Γ]
    {m : ℕ} (hm : 0 < m) (c : Γ) :
    Nat.card {P : (Γ →* ℂˣ) × ℂˣ // P.2 ^ m = P.1 c} = Nat.card Γ * m := by
  have := finite_hom_units_of_isCyclic Γ
  have : Fintype (Γ →* ℂˣ) := Fintype.ofFinite _
  have hfin : ∀ ν : Γ →* ℂˣ, Finite {ζ : ℂˣ // ζ ^ m = ν c} := fun ν =>
    Nat.finite_of_card_ne_zero (by rw [card_pow_eq m hm]; exact hm.ne')
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    fun (ν : Γ →* ℂˣ) (ζ : ℂˣ) => ζ ^ m = ν c), Nat.card_sigma]
  simp only [card_pow_eq m hm]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    card_hom_units_of_isCyclic]

theorem card_parameter_trivial_of_isCyclic (Γ : Type) [CommGroup Γ] {m : ℕ} (hm : 0 < m)
    (c : Γ) :
    Nat.card {P : {P : (Γ →* ℂˣ) × ℂˣ // P.2 ^ m = P.1 c} // P.1.1 = 1} = m := by
  let e : {P : {P : (Γ →* ℂˣ) × ℂˣ // P.2 ^ m = P.1 c} // P.1.1 = 1} ≃
      {ζ : ℂˣ // ζ ^ m = 1} :=
    { toFun := fun P => ⟨P.1.1.2, by rw [P.1.2, P.2]; rfl⟩
      invFun := fun ζ => ⟨⟨(1, ζ.1), by rw [ζ.2]; rfl⟩, rfl⟩
      left_inv := fun P => by
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext P.2.symm rfl
      right_inv := fun ζ => rfl }
  rw [Nat.card_congr e, card_pow_eq m hm]

theorem two_mul_ncard_pairs {α : Type} [Finite α] (w : α → α) (hw : Function.Involutive w)
    (S : Set α) (hS : ∀ P ∈ S, w P ∈ S ∧ w P ≠ P) :
    2 * Set.ncard ((fun P => ({P, w P} : Set α)) '' S) = Set.ncard S := by
  have : Fintype α := Fintype.ofFinite α
  set s := S.toFinset with hs
  set f := fun P => ({P, w P} : Set α) with hf
  have hpair : ∀ P Q : α, f P = f Q ↔ Q = P ∨ Q = w P := by
    intro P Q
    constructor
    · intro h
      have hQ : Q ∈ f P := by rw [h]; exact Set.mem_insert _ _
      rcases hQ with hQ | hQ
      · exact Or.inl hQ
      · exact Or.inr hQ
    · rintro (rfl | rfl)
      · rfl
      · simp only [hf, hw P]
        exact Set.pair_comm _ _
  have hfibre : ∀ x ∈ s.image f, (s.filter (fun P => f P = x)).card = 2 := by
    intro x hx
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hx
    have hP₀S : P₀ ∈ S := by simpa [hs] using hP₀
    have hfil : s.filter (fun P => f P = f P₀) = {P₀, w P₀} := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, hs,
        Set.mem_toFinset]
      constructor
      · rintro ⟨-, hQ⟩
        exact (hpair P₀ Q).mp hQ.symm
      · rintro (rfl | rfl)
        · exact ⟨hP₀S, rfl⟩
        · exact ⟨(hS P₀ hP₀S).1, ((hpair P₀ (w P₀)).mpr (Or.inr rfl)).symm⟩
    rw [hfil, Finset.card_pair (hS P₀ hP₀S).2.symm]
  have h2 : s.card = 2 * (s.image f).card := by
    rw [Finset.card_eq_sum_card_image f s, Finset.sum_congr rfl hfibre, Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hSs : S = ↑s := by simp [hs]
  rw [hSs, ← Finset.coe_image, Set.ncard_coe_finset, Set.ncard_coe_finset, h2]

end Counting

section Fixed

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}
  (z : Eˣ) (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b)
  (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0)

include hz in
theorem βE_mul_rE_val :
    (((βE F E basis z : normOne F E) : Eˣ) : E) * (((rE F E b h2 z hz : normOne F E) : Eˣ) : E) =
      -1 := by
  rw [βE_eq F E basis b h2 z hz]
  have hr : (((rE F E b h2 z hz : normOne F E) : Eˣ) : E) ≠ 0 := Units.ne_zero _
  simp only [negOneE, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_neg,
    Units.val_one, Units.val_inv_eq_inv_val]
  field_simp

include z hz in
theorem nonsplitTorus_fixed_iff (hb : ¬ IsSquare b) {g : CentralExtension F b m hm heven}
    (hg : g ∈ nonsplitTorus F b m hm heven E basis) :
    nonsplitWeyl F b m hm heven E basis h2 y hy * g *
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ = g ↔
      g ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  constructor
  · intro hfix
    obtain ⟨t, k, rfl⟩ := nonsplitTorus_normalForm z hz g hg
    rw [nonsplitWeyl_conj_normalForm z hz y hy h2] at hfix
    obtain ⟨ht, -⟩ := nonsplitTorus_normalForm_unique z hz hfix
    set β := βE F E basis z with hβ
    have hsq : β ^ (k : ℕ) = t * t := by
      calc β ^ (k : ℕ) = t * (t⁻¹ * β ^ (k : ℕ)) := by group
        _ = t * t := by rw [ht]
    have hsqE : ((β : Eˣ) : E) ^ (k : ℕ) = ((t : Eˣ) : E) * ((t : Eˣ) : E) := by
      have h := congrArg (fun s : normOne F E => ((s : Eˣ) : E)) hsq
      simpa using h
    have hβ0 : ((β : Eˣ) : E) ≠ 0 := Units.ne_zero _
    rcases Nat.even_or_odd' (k : ℕ) with ⟨i, hi | hi⟩
    ·
      set r := rE F E b h2 z hz with hr
      have hβr := βE_mul_rE_val z hz h2 (basis := basis)
      have hone : (((t * r ^ i : normOne F E) : Eˣ) : E) *
          (((t * r ^ i : normOne F E) : Eˣ) : E) = 1 := by
        simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]
        rw [hi] at hsqE
        calc ((t : Eˣ) : E) * ((r : Eˣ) : E) ^ i * (((t : Eˣ) : E) * ((r : Eˣ) : E) ^ i)
            = (((t : Eˣ) : E) * ((t : Eˣ) : E)) * (((r : Eˣ) : E) ^ i) ^ 2 := by ring
          _ = (((β : Eˣ) : E) * ((r : Eˣ) : E)) ^ (2 * i) := by rw [← hsqE]; ring
          _ = 1 := by rw [hβr, pow_mul, neg_one_sq, one_pow]
      have hcases : t * r ^ i = 1 ∨ t * r ^ i = negOneE F E h2 := by
        rcases mul_self_eq_one_iff.mp hone with h1 | h1
        · exact Or.inl (Subtype.ext (Units.ext (h1.trans Units.val_one.symm)))
        · refine Or.inr (Subtype.ext (Units.ext ?_))
          rw [h1]
          simp [negOneE]
      have hcomm : Commute (nonsplitDiag F b m hm heven E basis r)
          (cyclicGenerator F b m hm heven ^ 2) := (cyclicGenerator_sq_comm F b m hm heven _).symm
      have hv : nonsplitGenerator F b m hm heven E basis z hz ^ (k : ℕ) =
          nonsplitDiag F b m hm heven E basis (r ^ i) *
            (cyclicGenerator F b m hm heven ^ 2) ^ i := by
        rw [hi, pow_mul, nonsplitGenerator_sq z hz h2, hcomm.mul_pow, map_pow]
      rw [hv, ← mul_assoc, ← map_mul]
      refine Subgroup.mul_mem _ ?_ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
      rcases hcases with h1 | h1
      · rw [h1, map_one]
        exact Subgroup.one_mem _
      · rw [h1, nonsplitDiag_negOneE (hm := hm) (heven := heven) (basis := basis) h2]
        obtain ⟨l, hl⟩ := id heven
        refine ⟨l, ?_⟩
        simp only [zpow_natCast]
        rw [← pow_mul]
        congr 1
        omega
    ·
      exfalso
      apply βE_not_isSquare F E basis b h2 hb z hz
      refine ⟨t * (β ^ i)⁻¹, Subtype.ext (Units.ext ?_)⟩
      rw [hi] at hsqE
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      have hβi : ((β : Eˣ) : E) ^ i ≠ 0 := pow_ne_zero _ hβ0
      rw [← hβ]
      field_simp
      linear_combination hsqE
  · intro hg'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
    rw [(Commute.zpow_left (cyclicGenerator_sq_comm F b m hm heven
      (nonsplitWeyl F b m hm heven E basis h2 y hy)) k).eq.symm, mul_inv_cancel_right]

end Fixed

section Characters

abbrev NonsplitParameter (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Algebra F E]
    (b : Fˣ) (m : ℕ) (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) : Type :=
  {P : (normOne F E →* ℂˣ) × ℂˣ // P.2 ^ m = P.1 (cMinus F E b m h2 z hz)}

variable (F : Type) [Field F] [Fintype F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (E : Type) [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E) (h2 : (2 : F) ≠ 0)
  (z : Eˣ) (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b)

@[expose] noncomputable def nonsplitCharacter (P : NonsplitParameter F E b m h2 z hz) :
    nonsplitTorus F b m hm heven E basis →* ℂˣ :=
  Classical.choose (nonsplitTorus_lift (hm := hm) (heven := heven) (basis := basis) z hz h2
    P.1.1 P.1.2 (fun _ => mul_comm _ _) P.2)

theorem nonsplitCharacter_spec (P : NonsplitParameter F E b m h2 z hz) :
    (∀ t, nonsplitCharacter F b m hm heven E basis h2 z hz P
        ⟨nonsplitDiag F b m hm heven E basis t, nonsplitDiag_mem t⟩ = P.1.1 t) ∧
      nonsplitCharacter F b m hm heven E basis h2 z hz P
        ⟨nonsplitGenerator F b m hm heven E basis z hz, nonsplitGenerator_mem z hz⟩ = P.1.2 :=
  (Classical.choose_spec (nonsplitTorus_lift (hm := hm) (heven := heven) (basis := basis) z hz
    h2 P.1.1 P.1.2 (fun _ => mul_comm _ _) P.2)).1

theorem nonsplitCharacter_unique (P : NonsplitParameter F E b m h2 z hz)
    (φ : nonsplitTorus F b m hm heven E basis →* ℂˣ)
    (h1 : ∀ t, φ ⟨nonsplitDiag F b m hm heven E basis t, nonsplitDiag_mem t⟩ = P.1.1 t)
    (h2' : φ ⟨nonsplitGenerator F b m hm heven E basis z hz, nonsplitGenerator_mem z hz⟩ =
      P.1.2) :
    φ = nonsplitCharacter F b m hm heven E basis h2 z hz P :=
  (Classical.choose_spec (nonsplitTorus_lift (hm := hm) (heven := heven) (basis := basis) z hz
    h2 P.1.1 P.1.2 (fun _ => mul_comm _ _) P.2)).2 φ ⟨h1, h2'⟩

@[expose] noncomputable def nonsplitDiagT : normOne F E →* nonsplitTorus F b m hm heven E basis :=
  (nonsplitDiag F b m hm heven E basis).codRestrict _ nonsplitDiag_mem

theorem nonsplitGenerator_pow_m_T :
    (⟨nonsplitGenerator F b m hm heven E basis z hz, nonsplitGenerator_mem z hz⟩ :
      nonsplitTorus F b m hm heven E basis) ^ m =
        nonsplitDiagT F b m hm heven E basis (cMinus F E b m h2 z hz) :=
  Subtype.ext (by simp [nonsplitDiagT, nonsplitGenerator_pow_m z hz h2])

@[expose] noncomputable def nonsplitCharacterEquiv :
    NonsplitParameter F E b m h2 z hz ≃ (nonsplitTorus F b m hm heven E basis →* ℂˣ) where
  toFun := nonsplitCharacter F b m hm heven E basis h2 z hz
  invFun φ := ⟨(φ.comp (nonsplitDiagT F b m hm heven E basis),
      φ ⟨nonsplitGenerator F b m hm heven E basis z hz, nonsplitGenerator_mem z hz⟩), by
    rw [← map_pow, nonsplitGenerator_pow_m_T F b m hm heven E basis h2 z hz]
    rfl⟩
  left_inv P := by
    obtain ⟨h1, h2'⟩ := nonsplitCharacter_spec F b m hm heven E basis h2 z hz P
    apply Subtype.ext
    refine Prod.ext (MonoidHom.ext fun t => ?_) h2'
    exact h1 t
  right_inv φ := (nonsplitCharacter_unique F b m hm heven E basis h2 z hz _ φ
    (fun _ => rfl) rfl).symm

include basis hm in
theorem card_nonsplitParameter :
    Nat.card (NonsplitParameter F E b m h2 z hz) = (Nat.card F + 1) * m := by
  have := finite_of_basis F E basis
  rw [card_parameter_of_isCyclic (normOne F E) hm, card_normOne F E basis]

include h2 z hz in
theorem card_nonsplitTorus_characters :
    Nat.card (nonsplitTorus F b m hm heven E basis →* ℂˣ) = m * (Nat.card F + 1) := by
  rw [← Nat.card_congr (nonsplitCharacterEquiv F b m hm heven E basis h2 z hz),
    card_nonsplitParameter F b m hm E basis h2 z hz, mul_comm]

include heven in
theorem cMinus_sq_mul :
    ((βE F E basis z ^ m * cMinus F E b m h2 z hz * cMinus F E b m h2 z hz :
      normOne F E) : Eˣ) = 1 := by
  apply Units.ext
  have hβr := βE_mul_rE_val z hz h2 (basis := basis)
  have hm2 : m / 2 * 2 = m := Nat.div_mul_cancel (even_iff_two_dvd.mp heven)
  simp only [cMinus, negOneE, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  calc (((βE F E basis z : normOne F E) : Eˣ) : E) ^ m *
        (-1 * (((rE F E b h2 z hz : normOne F E) : Eˣ) : E) ^ (m / 2)) *
        (-1 * (((rE F E b h2 z hz : normOne F E) : Eˣ) : E) ^ (m / 2))
      = (((βE F E basis z : normOne F E) : Eˣ) : E) ^ m *
          ((((rE F E b h2 z hz : normOne F E) : Eˣ) : E) ^ (m / 2)) ^ 2 := by ring
    _ = ((((βE F E basis z : normOne F E) : Eˣ) : E) *
          (((rE F E b h2 z hz : normOne F E) : Eˣ) : E)) ^ m := by
        rw [← pow_mul, hm2, mul_pow]
    _ = 1 := by rw [hβr, heven.neg_one_pow]

include heven in
theorem nonsplitWeylParameter_spec (P : NonsplitParameter F E b m h2 z hz) :
    (P.1.1 (βE F E basis z) * P.1.2) ^ m = P.1.1⁻¹ (cMinus F E b m h2 z hz) := by
  rw [mul_pow, P.2, ← map_pow, ← map_mul, MonoidHom.inv_apply, ← map_inv]
  congr 1
  rw [eq_inv_iff_mul_eq_one]
  exact Subtype.ext (cMinus_sq_mul F b m heven E basis h2 z hz)

include heven in
@[expose] noncomputable def nonsplitWeylParameter (P : NonsplitParameter F E b m h2 z hz) :
    NonsplitParameter F E b m h2 z hz :=
  ⟨(P.1.1⁻¹, P.1.1 (βE F E basis z) * P.1.2),
    nonsplitWeylParameter_spec F b m heven E basis h2 z hz P⟩

theorem nonsplitWeylParameter_fst (P : NonsplitParameter F E b m h2 z hz) :
    (nonsplitWeylParameter F b m heven E basis h2 z hz P).1 =
      (P.1.1⁻¹, P.1.1 (βE F E basis z) * P.1.2) := rfl

theorem nonsplitWeylParameter_involutive :
    Function.Involutive (nonsplitWeylParameter F b m heven E basis h2 z hz) := by
  intro P
  apply Subtype.ext
  refine Prod.ext (MonoidHom.ext fun t => ?_) ?_
  · change ((P.1.1 t)⁻¹)⁻¹ = P.1.1 t
    exact inv_inv _
  · change (P.1.1 (βE F E basis z))⁻¹ * (P.1.1 (βE F E basis z) * P.1.2) = P.1.2
    exact inv_mul_cancel_left _ _

theorem nonsplitWeylParameter_eq_self_iff (hb : ¬ IsSquare b)
    (P : NonsplitParameter F E b m h2 z hz) :
    nonsplitWeylParameter F b m heven E basis h2 z hz P = P ↔ P.1.1 = 1 := by
  have := finite_of_basis F E basis
  constructor
  · intro h
    have h1 : P.1.1⁻¹ = P.1.1 :=
      congrArg (fun Q : NonsplitParameter F E b m h2 z hz => Q.1.1) h
    have h3 : P.1.1 (βE F E basis z) * P.1.2 = P.1.2 :=
      congrArg (fun Q : NonsplitParameter F E b m h2 z hz => Q.1.2) h
    have hνβ : P.1.1 (βE F E basis z) = 1 := mul_eq_right.mp h3
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := normOne F E)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ (βE F E basis z))
    have hodd : Odd k := by
      by_contra hev
      rw [Int.not_odd_iff_even] at hev
      obtain ⟨j, hj⟩ := hev
      exact βE_not_isSquare F E basis b h2 hb z hz ⟨g₀ ^ j, by rw [← hk, hj, _root_.zpow_add]⟩
    have hsq : P.1.1 g₀ * P.1.1 g₀ = 1 := by
      have h4 := congrArg (fun χ : normOne F E →* ℂˣ => χ g₀) h1
      simp only [MonoidHom.inv_apply] at h4
      calc P.1.1 g₀ * P.1.1 g₀ = (P.1.1 g₀)⁻¹ * P.1.1 g₀ := by rw [h4]
        _ = 1 := inv_mul_cancel _
    have hg : P.1.1 g₀ = 1 := by
      obtain ⟨j, hj⟩ := hodd
      have h4 : P.1.1 (g₀ ^ k) = P.1.1 g₀ ^ k := map_zpow _ _ _
      rw [hk, hνβ, hj, _root_.zpow_add, _root_.zpow_mul, zpow_one, zpow_two, hsq,
        _root_.one_zpow, one_mul] at h4
      exact h4.symm
    refine MonoidHom.ext fun x => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ x)
    rw [map_zpow, hg, _root_.one_zpow, MonoidHom.one_apply]
  · intro h
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · refine MonoidHom.ext fun x => ?_
      change (P.1.1 x)⁻¹ = P.1.1 x
      simp [h]
    · change P.1.1 (βE F E basis z) * P.1.2 = P.1.2
      simp [h]

variable (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1)

include z hz in
@[expose] noncomputable def nonsplitWeylConj :
    nonsplitTorus F b m hm heven E basis →* nonsplitTorus F b m hm heven E basis where
  toFun g := ⟨(nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g *
      nonsplitWeyl F b m hm heven E basis h2 y hy, nonsplitWeyl_inv_conj_mem z hz y hy h2 g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem nonsplitWeylConj_apply (g : nonsplitTorus F b m hm heven E basis) :
    (nonsplitWeylConj F b m hm heven E basis h2 z hz y hy g : CentralExtension F b m hm heven) =
      (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g *
        nonsplitWeyl F b m hm heven E basis h2 y hy := rfl

theorem nonsplitCharacter_comp_weylConj (P : NonsplitParameter F E b m h2 z hz) :
    (nonsplitCharacter F b m hm heven E basis h2 z hz P).comp
        (nonsplitWeylConj F b m hm heven E basis h2 z hz y hy) =
      nonsplitCharacter F b m hm heven E basis h2 z hz
        (nonsplitWeylParameter F b m heven E basis h2 z hz P) := by
  obtain ⟨hs1, hs2⟩ := nonsplitCharacter_spec F b m hm heven E basis h2 z hz P
  apply nonsplitCharacter_unique
  · intro t
    rw [MonoidHom.comp_apply]
    have hc : nonsplitWeylConj F b m hm heven E basis h2 z hz y hy
        ⟨nonsplitDiag F b m hm heven E basis t, nonsplitDiag_mem t⟩ =
          ⟨nonsplitDiag F b m hm heven E basis t⁻¹, nonsplitDiag_mem t⁻¹⟩ := by
      apply Subtype.ext
      rw [nonsplitWeylConj_apply, nonsplitWeyl_inv_conj y hy h2,
        nonsplitWeyl_conj_nonsplitDiag y hy h2]
    rw [hc, hs1, map_inv]
    rfl
  · rw [MonoidHom.comp_apply]
    have hc : nonsplitWeylConj F b m hm heven E basis h2 z hz y hy
        ⟨nonsplitGenerator F b m hm heven E basis z hz, nonsplitGenerator_mem z hz⟩ =
          ⟨nonsplitDiag F b m hm heven E basis (βE F E basis z), nonsplitDiag_mem _⟩ *
            ⟨nonsplitGenerator F b m hm heven E basis z hz, nonsplitGenerator_mem z hz⟩ := by
      apply Subtype.ext
      rw [nonsplitWeylConj_apply, nonsplitWeyl_inv_conj y hy h2,
        nonsplitWeyl_conj_nonsplitGenerator' z hz y hy h2]
      rfl
    rw [hc, map_mul, hs1, hs2]
    rfl

theorem nonsplitCharacter_x (P : NonsplitParameter F E b m h2 z hz)
    (hx : cyclicGenerator F b m hm heven ^ m ∈ nonsplitTorus F b m hm heven E basis) :
    nonsplitCharacter F b m hm heven E basis h2 z hz P ⟨cyclicGenerator F b m hm heven ^ m, hx⟩ =
      P.1.1 (negOneE F E h2) := by
  have h : (⟨cyclicGenerator F b m hm heven ^ m, hx⟩ : nonsplitTorus F b m hm heven E basis) =
      ⟨nonsplitDiag F b m hm heven E basis (negOneE F E h2), nonsplitDiag_mem _⟩ :=
    Subtype.ext (nonsplitDiag_negOneE (hm := hm) (heven := heven) (basis := basis) h2).symm
  rw [h, (nonsplitCharacter_spec F b m hm heven E basis h2 z hz P).1]

include hm basis in
theorem nonsplitParameter_orbits (hb : ¬ IsSquare b) :
    Set.ncard {P : NonsplitParameter F E b m h2 z hz | P.1.1 ≠ 1} = m * Nat.card F ∧
      Set.ncard ((fun P => ({P, nonsplitWeylParameter F b m heven E basis h2 z hz P} :
        Set (NonsplitParameter F E b m h2 z hz))) ''
          {P : NonsplitParameter F E b m h2 z hz | P.1.1 ≠ 1}) = m * Nat.card F / 2 := by
  have hcard := card_nonsplitParameter F b m hm E basis h2 z hz
  have hfin : Finite (NonsplitParameter F E b m h2 z hz) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact Nat.mul_ne_zero (by omega) hm.ne')
  have : Fintype (NonsplitParameter F E b m h2 z hz) := Fintype.ofFinite _
  have htriv := card_parameter_trivial_of_isCyclic (normOne F E) hm (cMinus F E b m h2 z hz)
  have hS : Set.ncard {P : NonsplitParameter F E b m h2 z hz | P.1.1 ≠ 1} = m * Nat.card F := by
    have h1 : Set.ncard {P : NonsplitParameter F E b m h2 z hz | P.1.1 = 1} = m := by
      rw [← Nat.card_coe_set_eq]
      exact htriv
    have hsum := Set.ncard_add_ncard_compl {P : NonsplitParameter F E b m h2 z hz | P.1.1 = 1}
    rw [h1, hcard] at hsum
    have h3 : {P : NonsplitParameter F E b m h2 z hz | P.1.1 = 1}ᶜ =
        {P : NonsplitParameter F E b m h2 z hz | P.1.1 ≠ 1} := rfl
    rw [h3] at hsum
    have h4 : (Nat.card F + 1) * m = m * Nat.card F + m := by ring
    omega
  refine ⟨hS, ?_⟩
  have h2m := two_mul_ncard_pairs (nonsplitWeylParameter F b m heven E basis h2 z hz)
    (nonsplitWeylParameter_involutive F b m heven E basis h2 z hz)
    {P : NonsplitParameter F E b m h2 z hz | P.1.1 ≠ 1} (fun P hP => ⟨fun h => hP ?_, fun h =>
      hP ((nonsplitWeylParameter_eq_self_iff F b m heven E basis h2 z hz hb P).mp h)⟩)
  · rw [hS] at h2m
    omega
  · refine MonoidHom.ext fun c => ?_
    have h5 := DFunLike.congr_fun h c
    rw [nonsplitWeylParameter_fst] at h5
    simpa using h5

end Characters

end CFSG.Wreathed.CentralSL2
