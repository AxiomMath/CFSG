module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersBasic
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersTools

public section

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.CentralSL2 CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped Pointwise

section Conjugation

variable {A G : Type*} [Group A] [Group G]

theorem nonsplit_ncard_conj_mul_card (φ : A →* G) (y : G) :
    (Set.range fun a => φ a * y * (φ a)⁻¹).ncard * Nat.card {a : A // φ a * y = y * φ a} =
      Nat.card A := by
  let : MulAction A G := MulAction.compHom G (MulAut.conj.comp φ)
  have hstab : Nat.card (MulAction.stabilizer A y) = Nat.card {a : A // φ a * y = y * φ a} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by
      change φ a * y * (φ a)⁻¹ = y ↔ _
      rw [mul_inv_eq_iff_eq_mul])
  rw [← hstab]
  change (MulAction.orbit A y).ncard * _ = _
  rw [← MulAction.index_stabilizer, Subgroup.index_mul_card]

theorem nonsplit_dvd_ncard (φ : A →* G) {S : Set G} (hS : S.Finite)
    (hinv : ∀ a, ∀ z ∈ S, φ a * z * (φ a)⁻¹ ∈ S) {n s : ℕ} (hs : 0 < s)
    (hsn : s * n = Nat.card A) (hcard : ∀ z ∈ S, Nat.card {a : A // φ a * z = z * φ a} = s) :
    n ∣ S.ncard := by
  let : MulAction A G := MulAction.compHom G (MulAut.conj.comp φ)
  refine dvd_ncard_of_card_orbit (A := A) hS hinv fun z hz => ?_
  have h := nonsplit_ncard_conj_mul_card φ z
  rw [hcard z hz, ← hsn, mul_comm s n] at h
  rw [Nat.card_coe_set_eq]
  exact Nat.eq_of_mul_eq_mul_right hs h

theorem nonsplit_eq_of_conj_eq {c z t : G} (hct : c * t = t * c) (h : c * z * c⁻¹ = t) :
    z = t := by
  calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
    _ = c⁻¹ * (t * c) := by rw [h, mul_assoc]
    _ = c⁻¹ * (c * t) := by rw [hct]
    _ = t := by group

theorem nonsplit_le_centralizer_of_permutable [Finite G] {U : Subgroup G} {x y : G}
    (hx : ∀ g, g * x = x * g)
    (hperm : (U : Set G) * (Subgroup.centralizer {y} : Set G) =
      (Subgroup.centralizer {y} : Set G) * U)
    (hU : Odd (Nat.card U)) {N : ℕ} (hN : (Subgroup.centralizer {y}).index = N)
    (φ : A →* G) (hφ : ∀ a, φ a * y = y * φ a) {n s : ℕ} (hn : Even n) (hs : 0 < s)
    (hsn : s * n = Nat.card A)
    (hcard : ∀ g ∈ permProduct U (Subgroup.centralizer {y}) hperm, g * y * g⁻¹ ≠ y →
      g * y * g⁻¹ ≠ x * y → Nat.card {a : A // φ a * (g * y * g⁻¹) = g * y * g⁻¹ * φ a} = s)
    (harith : ∀ k j : ℕ, k ∣ N → k = 1 + n * j → k = 1) :
    U ≤ Subgroup.centralizer {y} := by
  set K := permProduct U (Subgroup.centralizer {y}) hperm
  set J : Set G := Set.range fun k : K => (k : G) * y * (k : G)⁻¹
  have hφC : ∀ a, φ a ∈ Subgroup.centralizer {y} := fun a =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hφ a)
  have hφx : ∀ a, φ a * (x * y) = x * y * φ a := fun a => by
    rw [← mul_assoc, hx, mul_assoc, hφ, ← mul_assoc]
  have hJU : J = Set.range fun g : U => (g : G) * y * (g : G)⁻¹ := by
    ext z
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      obtain ⟨g, hg, c, hc, rfl⟩ := mem_permProduct.mp hk
      have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      refine ⟨⟨g, hg⟩, ?_⟩
      change g * y * g⁻¹ = g * c * y * (g * c)⁻¹
      calc g * y * g⁻¹ = g * (c * y * c⁻¹) * g⁻¹ := by rw [hcy, mul_inv_cancel_right]
        _ = g * c * y * (g * c)⁻¹ := by group
    · rintro ⟨⟨g, hg⟩, rfl⟩
      exact ⟨⟨g, left_le_permProduct hperm hg⟩, rfl⟩
  have hJodd : Odd J.ncard := by
    have h := nonsplit_ncard_conj_mul_card U.subtype y
    rw [hJU]
    exact hU.of_dvd_nat (Dvd.intro _ h)
  have hJK : J.ncard * Nat.card (Subgroup.centralizer {y}) = Nat.card K := by
    have h := nonsplit_ncard_conj_mul_card K.subtype y
    have hc : Nat.card {k : K // K.subtype k * y = y * K.subtype k} =
        Nat.card (Subgroup.centralizer {y}) :=
      Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ K))
        (q := fun x => x * y = y * x) fun hx =>
          right_le_permProduct hperm (Subgroup.mem_centralizer_singleton_iff.mpr hx)).trans
        (Equiv.subtypeEquivRight fun x => Subgroup.mem_centralizer_singleton_iff.symm))
    rw [hc] at h
    exact h
  have hJN : J.ncard ∣ N := by
    refine ⟨K.index, Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Subgroup.centralizer {y})) ?_⟩
    rw [← hN, Subgroup.card_mul_index, ← Subgroup.card_mul_index K, ← hJK]
    ring
  have hyJ : y ∈ J := ⟨1, by simp⟩
  have hSdvd : n ∣ (J \ {y, x * y}).ncard := by
    refine nonsplit_dvd_ncard φ (Set.toFinite _) ?_ hs hsn ?_
    · rintro a z ⟨⟨k, rfl⟩, hz⟩
      refine ⟨⟨⟨φ a * k, K.mul_mem (right_le_permProduct hperm (hφC a)) k.2⟩, ?_⟩, ?_⟩
      · change φ a * k * y * (φ a * k)⁻¹ = φ a * (k * y * (k : G)⁻¹) * (φ a)⁻¹
        group
      · rintro (h | h)
        · exact hz (Or.inl (nonsplit_eq_of_conj_eq (hφ a) h))
        · exact hz (Or.inr (nonsplit_eq_of_conj_eq (hφx a) h))
    · rintro z ⟨⟨k, rfl⟩, hz⟩
      exact hcard k k.2 (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h))
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard J {y, x * y}
  have hle : (J ∩ {y, x * y}).ncard ≤ 2 :=
    (Set.ncard_le_ncard Set.inter_subset_right).trans
      ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  have hge : 1 ≤ (J ∩ {y, x * y}).ncard :=
    (Set.ncard_pos).mpr ⟨y, hyJ, Set.mem_insert y _⟩
  obtain ⟨j, hj⟩ := hSdvd
  have h2 : 2 ∣ (J \ {y, x * y}).ncard := (even_iff_two_dvd.mp hn).trans ⟨j, hj⟩
  have hone : J.ncard = 1 := harith _ j hJN (by
    rw [← hj]
    obtain ⟨r, hr⟩ := hJodd
    omega)
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hone
  intro g hg
  have hgJ : g * y * g⁻¹ ∈ J := ⟨⟨g, left_le_permProduct hperm hg⟩, rfl⟩
  rw [hz] at hgJ hyJ
  have hgy : g * y * g⁻¹ = y := hgJ.trans hyJ.symm
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * y = g * y * g⁻¹ * g := by group
    _ = y * g := by rw [hgy]

end Conjugation

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem nonsplit_trace_matrixConjugation_weyl (G : GL (Fin 2) F) :
    matrixConjugation F G (weyl F) 0 0 + matrixConjugation F G (weyl F) 1 1 = 0 := by
  have h : ((matrixConjugation F G (weyl F) : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = (G : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have h1 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F))
      (matrixConjugation_toGL F G (weyl F))
    simpa only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, weyl_val] using h1
  have htr := Matrix.trace_units_conj G !![(0 : F), -1; 1, 0]
  rw [← h, Matrix.trace_fin_two, Matrix.trace_fin_two] at htr
  simpa using htr

theorem nonsplit_mk_eq_one_of_commute {P : GL (Fin 2) F}
    (hP : P * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * P)
    (h10 : P.val 1 0 = 0) : Matrix.ProjGenLinGroup.mk P = 1 := by
  obtain ⟨h11, h01⟩ := entries_of_commute_weyl hP
  rw [h10, neg_zero] at h01
  have h00 : P.val 0 0 ≠ 0 := by
    intro h0
    have hdet := GeneralLinearGroup.det_ne_zero P
    rw [det_fin_two] at hdet
    apply hdet
    change P.val 0 0 * P.val 1 1 - P.val 0 1 * P.val 1 0 = 0
    rw [h0, h10]
    ring
  have hs : P = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (P.val 0 0) h00) := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]
  rw [hs, Matrix.ProjGenLinGroup.mk_scalar]

theorem nonsplit_mem_zpowers_of_commute (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b)
    {h : SemilinearExtension F b m hm heven Sigma hSigma} {w : CentralExtension F b m hm heven}
    (hw : w ∈ Subgroup.centralizer {involutionY F b m hm heven})
    (hy : h * modelY b m hm heven Sigma hSigma * h⁻¹ ≠ modelY b m hm heven Sigma hSigma)
    (hxy : h * modelY b m hm heven Sigma hSigma * h⁻¹ ≠
      modelX b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma)
    (hc : SemidirectProduct.inl w * (h * modelY b m hm heven Sigma hSigma * h⁻¹) =
      h * modelY b m hm heven Sigma hSigma * h⁻¹ * SemidirectProduct.inl w) :
    w ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  obtain ⟨G, hG⟩ := exists_projectiveMap_eq h.left
  obtain ⟨P, hP⟩ := exists_projectiveMap_eq w
  have hPJ := (mem_centralizer_involutionY_iff hP).mp hw
  rw [conj_modelY hG] at hy hxy hc
  rw [← map_mul, ← map_mul] at hc
  have hc' := SemidirectProduct.inl_injective hc
  have ha : (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) * w =
      w * (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) :=
    (Commute.pow_left (cyclicGenerator_sq_comm F b m hm heven w) (m / 4)).eq
  have hconj : w * specialInclusion F b m hm heven (matrixConjugation F G (weyl F)) * w⁻¹ =
      specialInclusion F b m hm heven (matrixConjugation F G (weyl F)) := by
    apply mul_left_cancel (a := (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4))
    calc (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
          (w * specialInclusion F b m hm heven (matrixConjugation F G (weyl F)) * w⁻¹)
        = (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) * w *
          specialInclusion F b m hm heven (matrixConjugation F G (weyl F)) * w⁻¹ := by group
      _ = w * ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
          specialInclusion F b m hm heven (matrixConjugation F G (weyl F))) * w⁻¹ := by
        rw [ha]
        group
      _ = (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
          specialInclusion F b m hm heven (matrixConjugation F G (weyl F)) := by
        rw [hc']
        group
  rw [conj_specialInclusion_eq hP] at hconj
  have hmc := specialInclusion_injective F b m hm heven hconj
  have hPJ' : P * SpecialLinearGroup.toGL (matrixConjugation F G (weyl F)) =
      SpecialLinearGroup.toGL (matrixConjugation F G (weyl F)) * P := by
    have h1 := congrArg SpecialLinearGroup.toGL hmc
    rw [matrixConjugation_toGL] at h1
    calc P * SpecialLinearGroup.toGL (matrixConjugation F G (weyl F))
        = P * SpecialLinearGroup.toGL (matrixConjugation F G (weyl F)) * P⁻¹ * P := by group
      _ = SpecialLinearGroup.toGL (matrixConjugation F G (weyl F)) * P := by rw [h1]
  by_cases h10 : P.val 1 0 = 0
  · rw [← projectiveMap_eq_one_iff hb, hP]
    exact nonsplit_mk_eq_one_of_commute hPJ h10
  · exfalso
    rcases eq_weyl_or_eq_inv_of_commute h2 hPJ h10
        (nonsplit_trace_matrixConjugation_weyl G) hPJ' with hJ | hJ
    · exact hy (by rw [hJ]; rfl)
    · exact hxy (by rw [hJ, modelX_mul_modelY])

theorem nonsplit_card_commute_conj (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b)
    {h : SemilinearExtension F b m hm heven Sigma hSigma}
    (hy : h * modelY b m hm heven Sigma hSigma * h⁻¹ ≠ modelY b m hm heven Sigma hSigma)
    (hxy : h * modelY b m hm heven Sigma hSigma * h⁻¹ ≠
      modelX b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma) :
    Nat.card {w : Subgroup.centralizer {involutionY F b m hm heven} //
      (SemidirectProduct.inl (w : CentralExtension F b m hm heven) :
          SemilinearExtension F b m hm heven Sigma hSigma) *
          (h * modelY b m hm heven Sigma hSigma * h⁻¹) =
        h * modelY b m hm heven Sigma hSigma * h⁻¹ *
          SemidirectProduct.inl (w : CentralExtension F b m hm heven)} = m := by
  have hcen : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ≤
      Subgroup.center (CentralExtension F b m hm heven) :=
    Subgroup.zpowers_le.mpr (cyclicGenerator_sq_mem_center F b m hm heven)
  have hle : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ≤
      Subgroup.centralizer {involutionY F b m hm heven} := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp (hcen hv) _).symm
  obtain ⟨G, hG⟩ := exists_projectiveMap_eq h.left
  have hiff : ∀ w : Subgroup.centralizer {involutionY F b m hm heven},
      (SemidirectProduct.inl (w : CentralExtension F b m hm heven) :
          SemilinearExtension F b m hm heven Sigma hSigma) *
          (h * modelY b m hm heven Sigma hSigma * h⁻¹) =
        h * modelY b m hm heven Sigma hSigma * h⁻¹ *
          SemidirectProduct.inl (w : CentralExtension F b m hm heven) ↔
      (w : CentralExtension F b m hm heven) ∈
        Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
    intro w
    refine ⟨nonsplit_mem_zpowers_of_commute h2 hb w.2 hy hxy, fun hw => ?_⟩
    rw [conj_modelY hG, ← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp (hcen hw) _).symm
  refine (Nat.card_congr ((Equiv.subtypeEquivRight hiff).trans
    (Equiv.subtypeSubtypeEquivSubtype fun hv => hle hv))).trans ?_
  exact (Nat.card_zpowers _).trans (orderOf_cyclicGenerator_sq F b m hm heven h2)

theorem le_modelC_of_permutable [Fintype F] (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b)
    (hd : Odd (Nat.card Sigma)) (hsq : ¬ IsSquare (-1 : F))
    {U : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hU : Odd (Nat.card U))
    (hperm : (U : Set (SemilinearExtension F b m hm heven Sigma hSigma)) *
        (modelC b m hm heven Sigma hSigma : Set (SemilinearExtension F b m hm heven Sigma hSigma)) =
      (modelC b m hm heven Sigma hSigma : Set (SemilinearExtension F b m hm heven Sigma hSigma)) *
        (U : Set (SemilinearExtension F b m hm heven Sigma hSigma))) :
    U ≤ modelC b m hm heven Sigma hSigma := by
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hqodd : Odd (Nat.card F) := by
    have hc : ringChar F ≠ 2 := fun h => h2 (by
      have := ringChar.Nat.cast_ringChar (R := F)
      rw [h] at this
      exact_mod_cast this)
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hc
  have hq3 : 3 ≤ Nat.card F := by
    obtain ⟨r, hr⟩ := hqodd
    omega
  have hCV : Nat.card (Subgroup.centralizer {involutionY F b m hm heven}) =
      m * (Nat.card F + 1) := by
    rw [card_centralizer_involutionY hb, ite_eq_right hsq]
  have hC : Nat.card (Subgroup.centralizer {modelY b m hm heven Sigma hSigma}) =
      m * (Nat.card F + 1) * Nat.card Sigma := by
    rw [← hCV]
    exact card_modelC
  refine nonsplit_le_centralizer_of_permutable (x := modelX b m hm heven Sigma hSigma)
    modelX_comm hperm hU (N := Nat.card F * (Nat.card F - 1)) ?_
    (SemidirectProduct.inl.comp (Subgroup.centralizer {involutionY F b m hm heven}).subtype)
    (fun a => Subgroup.mem_centralizer_singleton_iff.mp ((inl_mem_modelC_iff _).mpr a.2))
    (n := Nat.card F + 1) (s := m) ?_ hm (by rw [hCV]) ?_ ?_
  ·
    have hsq1 : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      have h1 : 1 ≤ Nat.card F := by omega
      have h1' : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1, h1']
      ring
    have h1 := Subgroup.card_mul_index (Subgroup.centralizer {modelY b m hm heven Sigma hSigma})
    rw [hC, card_semilinearExtension, card_SL_two F, hsq1] at h1
    have hpos : 0 < m * (Nat.card F + 1) * Nat.card Sigma :=
      Nat.mul_pos (Nat.mul_pos hm (Nat.succ_pos _)) hd.pos
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h1]
    ring
  · obtain ⟨r, hr⟩ := hqodd
    exact ⟨r + 1, by omega⟩
  · intro g _ hy hxy
    exact nonsplit_card_commute_conj h2 hb hy hxy
  · intro k j hk hj
    exact eq_one_of_dvd_of_eq_one_add hqodd hq3 hk hj

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
