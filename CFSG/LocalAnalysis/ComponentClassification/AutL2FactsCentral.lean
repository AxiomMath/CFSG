module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylowModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsRank
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylow
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsNT
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStab

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open scoped Pointwise

universe u

variable {F : Type u} [Field F] [Finite F]

theorem card_linearPart_le_two (hodd : IsOddPrimePower (Nat.card F)) (T : Subgroup (PSL2 F))
    (hT2 : IsPGroup 2 T) {a b : PSL2 F} (ha : a ∈ T) (hb : b ∈ T) (hab : a * b ≠ b * a)
    (R : Subgroup (PGammaL2 F)) (hR : IsPGroup 2 R)
    (hRT : ∀ r ∈ R, ∀ t ∈ T, r * incl F t = incl F t * r) :
    Nat.card (linearPart R) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := linearPart R
  have hL2 : IsPGroup 2 L := hR.comap_of_injective _ SemidirectProduct.inl_injective
  set T' := T.map (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))
  have hT'2 : IsPGroup 2 T' := hT2.map _
  have hcomm : ∀ g ∈ L, ∀ t ∈ T', g * t = t * g := by
    rintro g hg _ ⟨t, ht, rfl⟩
    have h := hRT _ hg t ht
    rw [incl_apply, ← map_mul, ← map_mul] at h
    exact SemidirectProduct.inl_injective h
  have hLN : L ≤ normalizer (T' : Set (PGL2 F)) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      rw [hcomm g hg t ht, mul_inv_cancel_right]
      exact ht
    · intro ht
      have hs := hcomm g hg _ ht
      have : t = g * t * g⁻¹ := by
        calc t = g⁻¹ * ((g * t * g⁻¹) * g) := by group
          _ = g⁻¹ * (g * (g * t * g⁻¹)) := by rw [hs]
          _ = g * t * g⁻¹ := by group
      rw [this]
      exact ht
  obtain ⟨S, hS⟩ := (hL2.to_sup_of_normal_right' hT'2 hLN).exists_le_sylow
  obtain ⟨m, hm, ⟨φ⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hodd S
  have hLS : L ≤ (S : Subgroup (PGL2 F)) := le_sup_left.trans hS
  have hT'S : T' ≤ (S : Subgroup (PGL2 F)) := le_sup_right.trans hS
  have haS : Matrix.ProjectiveSpecialLinearGroup.toPGL a ∈ (S : Subgroup (PGL2 F)) :=
    hT'S ⟨a, ha, rfl⟩
  have hbS : Matrix.ProjectiveSpecialLinearGroup.toPGL b ∈ (S : Subgroup (PGL2 F)) :=
    hT'S ⟨b, hb, rfl⟩
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  have hab' : φ ⟨_, haS⟩ * φ ⟨_, hbS⟩ ≠ φ ⟨_, hbS⟩ * φ ⟨_, haS⟩ := by
    intro h
    apply hab
    rw [← map_mul, ← map_mul] at h
    have h1 := congrArg Subtype.val (φ.injective h)
    simp only [Subgroup.coe_mul] at h1
    rw [← map_mul, ← map_mul] at h1
    exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h1
  have key := dihedral_card_le_two_of_commute _ _ hab' ((L.subgroupOf S).map φ.toMonoidHom)
    (by
      rintro _ ⟨g, hg, rfl⟩
      have hg' : (g : PGL2 F) ∈ L := hg
      constructor
      · rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hcomm _ hg' _ ⟨a, ha, rfl⟩)
      · rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hcomm _ hg' _ ⟨b, hb, rfl⟩))
  rw [Subgroup.card_map_of_injective φ.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLS).toEquiv] at key
  exact key

theorem fieldProj_sq_of_commute_tor {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (x : PGammaL2 F) {μ : Fˣ} (hμ : orderOf μ = 2 ^ (twoVal F - 1))
    (hn : 2 ≤ twoVal F)
    (hx : x * SemidirectProduct.inl (tor F μ) = SemidirectProduct.inl (tor F μ) * x)
    {k : ℕ} (hk : x.right ^ 2 ^ k = 1) : x.right ^ 2 = 1 := by
  have hμ1 : μ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hμ
    have : 2 ≤ 2 ^ (twoVal F - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (twoVal F - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨a, ε, hxa⟩ := exists_nm_of_conj_tor x hμ1 (ν := μ) (by rw [hx, mul_inv_cancel_right])
  have htw := (nm_commute_tor_iff a μ ε x.right).mp (by rw [← hxa, ← inl_tor]; exact hx)
  have hfix : fu F x.right μ = μ ∨ fu F x.right μ = μ⁻¹ := by
    cases ε
    · exact Or.inl htw
    · right
      simp only [twist_true] at htw
      exact inv_eq_iff_eq_inv.mp htw
  obtain ⟨e, he, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  by_cases he1 : e ≤ 1
  · apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hord]
    exact Nat.pow_dvd_pow 2 he1
  · exfalso
    have hdvd := two_pow_add_dvd_of_fix_or_inv hp hp2 hF x.right (by omega) hord μ hμ hfix
    apply not_two_pow_twoVal_succ_dvd F Finite.one_lt_card
    exact (Nat.pow_dvd_pow 2 (by omega)).trans hdvd

theorem pow_mod_four_of_even {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : Even f) :
    p ^ f % 4 = 1 := by
  obtain ⟨g, rfl⟩ := hf
  rw [← two_mul, pow_mul']
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := g)
  rw [hk, show (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 by ring]
  omega

theorem card_le_four_of_centralizes_sylow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (T : Sylow 2 (PSL2 F)) (hT : 8 ≤ Nat.card T)
    (R : Subgroup (PGammaL2 F)) (hR : IsPGroup 2 R)
    (hRT : ∀ r ∈ R, ∀ t ∈ (T : Subgroup (PSL2 F)), r * incl F t = incl F t * r) :
    Nat.card R ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  obtain ⟨m, -, ⟨φ⟩⟩ := sylow_two_dihedral_of_equiv (MulEquiv.refl (PSL2 F)) hodd T
  have hcard : Nat.card T = 2 ^ (m + 1) := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  have hm : 2 ≤ m := by
    rw [hcard] at hT
    by_contra h
    push Not at h
    interval_cases m <;> simp_all
  have hnc : ∃ a b : DihedralGroup (2 ^ m), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    exact DihedralGroup.not_commutative (n := 2 ^ m) (by omega) (by omega) ⟨⟨h⟩⟩
  obtain ⟨a₁, b₁, hnc⟩ := hnc
  have hab : (φ.symm a₁ : PSL2 F) * φ.symm b₁ ≠ φ.symm b₁ * φ.symm a₁ := by
    intro h
    apply hnc
    apply φ.symm.injective
    rw [map_mul, map_mul]
    exact Subtype.ext h
  have h1 := card_linearPart_le_two hodd T T.isPGroup' (φ.symm _).2 (φ.symm _).2 hab R hR hRT
  have h2 : Nat.card (R.map (fieldProj F)) ≤ 2 := by
    apply card_le_two_of_sq_ringAut
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
    have hk' : x.right ^ 2 ^ k = 1 := by
      have := congrArg (fun y : R => fieldProj F (y : PGammaL2 F)) hk
      simp only [SubgroupClass.coe_pow, map_pow, OneMemClass.coe_one, map_one] at this
      exact this
    rw [← pow_two]
    change x.right ^ 2 = 1
    rcases Nat.even_or_odd f with hfe | hfo
    · have hq4 : Nat.card F % 4 = 1 := by rw [hF]; exact pow_mod_four_of_even hp hp2 hfe
      have hsq : IsSquare (-1 : F) := by
        have : Fintype F := Fintype.ofFinite F
        classical
        rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
        omega
      obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hodd hsq hq4) T
      have hn : 3 ≤ twoVal F := by
        have hc : Nat.card T = 2 ^ twoVal F := by
          rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity (stdSylow F hodd hsq hq4),
            coe_stdSylow, card_stdT hodd hsq]
        rw [hc] at hcard
        have := Nat.pow_right_injective (le_refl 2) hcard
        omega
      obtain ⟨t₀, ht₀⟩ := torSub_stdGen_le_range hsq ⟨stdGen F ^ 2, mem_zpowers _, false,
        (mul_one _).symm⟩
      have ht₀T : h * t₀ * h⁻¹ ∈ (T : Subgroup (PSL2 F)) := by
        rw [← hh, Sylow.coe_subgroup_smul]
        have := Subgroup.smul_mem_pointwise_smul t₀ (MulAut.conj h) _
          (show t₀ ∈ (stdSylow F hodd hsq hq4 : Subgroup (PSL2 F)) by
            rw [coe_stdSylow]
            change Matrix.ProjectiveSpecialLinearGroup.toPGL t₀ ∈ torSub F _
            rw [ht₀]
            exact ⟨stdGen F ^ 2, mem_zpowers _, false, (mul_one _).symm⟩)
        simpa [MulAut.smul_def, MulAut.conj_apply] using this
      have hc := hRT x hx _ ht₀T
      set x' := (incl F h)⁻¹ * x * incl F h
      have hx' : x' * SemidirectProduct.inl (tor F (stdGen F ^ 2)) =
          SemidirectProduct.inl (tor F (stdGen F ^ 2)) * x' := by
        have e1 : incl F (h * t₀ * h⁻¹) = incl F h * SemidirectProduct.inl (tor F (stdGen F ^ 2)) *
            (incl F h)⁻¹ := by
          rw [map_mul, map_mul, map_inv, incl_apply F t₀, ht₀]
        rw [e1] at hc
        simp only [x']
        calc (incl F h)⁻¹ * x * incl F h * SemidirectProduct.inl (tor F (stdGen F ^ 2)) =
            (incl F h)⁻¹ * (x * (incl F h * SemidirectProduct.inl (tor F (stdGen F ^ 2)) *
              (incl F h)⁻¹)) * incl F h := by group
          _ = (incl F h)⁻¹ * ((incl F h * SemidirectProduct.inl (tor F (stdGen F ^ 2)) *
              (incl F h)⁻¹) * x) * incl F h := by rw [hc]
          _ = _ := by group
      have hright : x'.right = x.right := by
        simp [x', incl_apply]
      have := fieldProj_sq_of_commute_tor hp hp2 hF x' (orderOf_stdGen_sq hodd) (by omega) hx'
        (k := k) (by rw [hright]; exact hk')
      rw [hright] at this
      exact this
    · rw [eq_one_of_two_power_ringAut hp hF hfo x.right k hk', one_pow]
  rw [card_eq_linearPart_mul]
  calc Nat.card (linearPart R) * Nat.card (R.map (fieldProj F)) ≤ 2 * 2 :=
        Nat.mul_le_mul h1 h2
    _ = 4 := by norm_num

theorem centralizes_map_autEquiv {Y : Type*} [Group Y] (e : Y ≃* PSL2 F) (T : Subgroup Y)
    (R' : Subgroup (MulAut Y))
    (hR : R' ≤ centralizer ((T.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) :
      Set (MulAut Y))) :
    ∀ r ∈ R'.map (autEquiv e).toMonoidHom, ∀ t ∈ T.map e.toMonoidHom,
      r * incl F t = incl F t * r := by
  rintro _ ⟨r, hr, rfl⟩ _ ⟨t, ht, rfl⟩
  have h := mem_centralizer_iff.mp (hR hr) (MulAut.conj t) ⟨t, ht, rfl⟩
  change autEquiv e r * incl F (e t) = incl F (e t) * autEquiv e r
  rw [← autEquiv_conj, ← map_mul, ← map_mul, h]

@[expose] def sylowMap {Y : Type*} [Group Y] [Finite Y] (e : Y ≃* PSL2 F) (T : Sylow 2 Y) :
    Sylow 2 (PSL2 F) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T

omit [Finite F] in
theorem coe_sylowMap {Y : Type*} [Group Y] [Finite Y] (e : Y ≃* PSL2 F) (T : Sylow 2 Y) :
    (sylowMap e T : Subgroup (PSL2 F)) = (T : Subgroup Y).map e.toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective T

omit [Finite F] in
theorem card_sylowMap {Y : Type*} [Group Y] [Finite Y] (e : Y ≃* PSL2 F) (T : Sylow 2 Y) :
    Nat.card (sylowMap e T) = Nat.card T := by
  rw [coe_sylowMap, Subgroup.card_map_of_injective e.injective]

end CFSG.ComponentClassification.AutL2Facts
