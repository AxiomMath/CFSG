module

public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.ClassicalGroups.Unitary.Transitivity
public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary Subgroup
open CFSG.LieType.Universal.Unitary (SUid)

section Torus

variable {F : Type} [Field F] (σ : F ≃+* F)

noncomputable def diagSU (d : Fin 4 → F) (hd : ∀ i, σ (d i) * d i = 1) (hdet : ∏ i, d i = 1) :
    ↥(SUid σ 4) :=
  mkSU σ (Matrix.diagonal d) (by rw [Matrix.det_diagonal]; exact hdet) (by
    intro x y
    simp only [herm, Matrix.mulVec_diagonal, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (σ (x i) * y i) * hd i)

theorem diagSU_smul (d : Fin 4 → F) (hd : ∀ i, σ (d i) * d i = 1) (hdet : ∏ i, d i = 1)
    (v : Fin 4 → F) : diagSU σ d hd hdet • v = fun i => d i * v i := by
  rw [diagSU, mkSU_smul]
  funext i
  exact Matrix.mulVec_diagonal d v i

variable {σ}

def torusVec (a b : Fˣ) : Fin 4 → F := ![1, (a : F), (b : F), (((a * b)⁻¹ : Fˣ) : F)]

theorem torusVec_det (a b : Fˣ) : ∏ i, torusVec a b i = 1 := by
  rw [Fin.prod_univ_four]
  have h : ((a * b * (a * b)⁻¹ : Fˣ) : F) = 1 := by simp
  simpa [torusVec, mul_assoc] using h

theorem torusVec_norm {Z : Subgroup Fˣ} (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) {a b : Fˣ}
    (ha : a ∈ Z) (hb : b ∈ Z) (i : Fin 4) : σ (torusVec a b i) * torusVec a b i = 1 := by
  fin_cases i
  · simp [torusVec]
  · exact hZ a ha
  · exact hZ b hb
  · exact hZ _ (Z.inv_mem (Z.mul_mem ha hb))

theorem torusVec_mul (a a' b b' : Fˣ) (i : Fin 4) :
    torusVec (a * a') (b * b') i = torusVec a b i * torusVec a' b' i := by
  fin_cases i
  · simp [torusVec]
  · simp [torusVec]
  · simp [torusVec]
  · have h : (a * a' * (b * b'))⁻¹ = (a * b)⁻¹ * (a' * b')⁻¹ := by
      rw [← mul_inv]
      congr 1
      ac_rfl
    simp [torusVec, h]

noncomputable def torusSU (Z : Subgroup Fˣ) (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) :
    ↥Z × ↥Z →* ↥(SUid σ 4) where
  toFun x := diagSU σ (torusVec (x.1 : Fˣ) (x.2 : Fˣ)) (torusVec_norm hZ x.1.2 x.2.2)
    (torusVec_det _ _)
  map_one' := by
    apply ext_smul
    intro v
    rw [diagSU_smul, one_smul]
    funext i
    fin_cases i <;> simp [torusVec]
  map_mul' x y := by
    apply ext_smul
    intro v
    rw [mul_smul, diagSU_smul, diagSU_smul, diagSU_smul]
    funext i
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    rw [torusVec_mul, mul_assoc]

theorem torusSU_smul (Z : Subgroup Fˣ) (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) (x : ↥Z × ↥Z)
    (v : Fin 4 → F) :
    torusSU Z hZ x • v = fun i => torusVec (x.1 : Fˣ) (x.2 : Fˣ) i * v i :=
  diagSU_smul σ _ (torusVec_norm hZ x.1.2 x.2.2) (torusVec_det _ _) v

theorem torusSU_injective (Z : Subgroup Fˣ) (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) :
    Function.Injective (torusSU Z hZ) := by
  intro x y h
  have h1 := congrArg (fun g => g • (Pi.single 1 1 : Fin 4 → F)) h
  have h2 := congrArg (fun g => g • (Pi.single 2 1 : Fin 4 → F)) h
  simp only [torusSU_smul] at h1 h2
  have e1 := congrFun h1 1
  have e2 := congrFun h2 2
  simp [torusVec] at e1 e2
  exact Prod.ext (Subtype.ext (Units.ext e1)) (Subtype.ext (Units.ext e2))

theorem torusSU_smul_single_zero (Z : Subgroup Fˣ) (hZ : ∀ a ∈ Z, σ (a : F) * a = 1)
    (x : ↥Z × ↥Z) : torusSU Z hZ x • (Pi.single 0 1 : Fin 4 → F) = Pi.single 0 1 := by
  rw [torusSU_smul]
  funext i
  fin_cases i <;> simp [torusVec]

theorem torusSU_one_smul_eq (Z : Subgroup Fˣ) (hZ : ∀ a ∈ Z, σ (a : F) * a = 1) (b : ↥Z)
    {s : Fin 4 → F} (h2 : s 2 = 0) (h3 : s 3 = 0) :
    torusSU Z hZ ((1 : ↥Z), b) • s = s := by
  rw [torusSU_smul]
  funext i
  fin_cases i <;> simp [torusVec, h2, h3]

theorem isElemAbelian_range {A H : Type*} [CommGroup A] [Group H] (f : A →* H) {p : ℕ}
    (hA : ∀ x : A, x ^ p = 1) : IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    show (x : H) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := hx
    rw [← map_pow, hA, map_one]

theorem exists_stab_of_hom {A : Type} [CommGroup A] {p k : ℕ} (hA : ∀ x : A, x ^ p = 1)
    (hcard : Nat.card A = p ^ k) (Θ : A →* ↥(SUid σ 4)) (hΘ : Function.Injective Θ)
    {v w : Fin 4 → F} (hfix : ∀ x, Θ x • v = v) (t : ↥(SUid σ 4)) (htv : t • v = w) :
    ∃ E : Subgroup (GL (Fin 4) F), E ≤ SUid σ 4 ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k ∧
      ∀ g ∈ E, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ w = w := by
  set Ψ : A →* GL (Fin 4) F :=
    (SUid σ 4).subtype.comp ((MulAut.conj t).toMonoidHom.comp Θ) with hΨ
  have hinj : Function.Injective Ψ :=
    (SUid σ 4).subtype_injective.comp ((MulAut.conj t).injective.comp hΘ)
  have hΨa : ∀ a, Ψ a = ((t * Θ a * t⁻¹ : ↥(SUid σ 4)) : GL (Fin 4) F) := fun a => rfl
  refine ⟨Ψ.range, ?_, isElemAbelian_range Ψ hA, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    rw [hΨa]
    exact (t * Θ a * t⁻¹).2
  · rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · rintro _ ⟨a, rfl⟩
    have h : (t * Θ a * t⁻¹) • w = w := by
      rw [← htv, mul_smul, mul_smul, inv_smul_smul, hfix a]
    rw [hΨa]
    exact (CFSG.ClassicalGroups.Unitary.smul_def σ _ _).symm.trans h

end Torus

section Model

variable {F : Type} [Field F] [Finite F] {n p : ℕ}

theorem exists_torus_data (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hF : Nat.card F = (2 ^ n) ^ 2)
    {σ : F ≃+* F} (hσ : ∀ c, σ c * c = c ^ (2 ^ n + 1)) :
    ∃ Z : Subgroup Fˣ, (∀ a ∈ Z, a ^ p = 1) ∧ Nat.card Z = p ∧ ∀ a ∈ Z, σ (a : F) * a = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcardU : p ∣ Nat.card Fˣ := by
    rw [CFSG.ClassicalGroups.Unitary.card_units_of_card (p := 2) (f := n) hF]
    have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [CFSG.ClassicalGroups.Unitary.sq_sub_one_eq (2 ^ n) hq]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hcardU
  refine ⟨Subgroup.zpowers ζ, fun a ha => ?_, ?_, fun a ha => ?_⟩
  · exact orderOf_dvd_iff_pow_eq_one.mp (hζ ▸ orderOf_dvd_of_mem_zpowers ha)
  · rw [Nat.card_zpowers, hζ]
  · have h1 : a ^ (2 ^ n + 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp
        ((orderOf_dvd_of_mem_zpowers ha).trans (hζ ▸ hpq))
    rw [hσ, ← Units.val_pow_eq_pow_val, h1, Units.val_one]

theorem exists_stab_elemAbelian_nonsing (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hF : Nat.card F = (2 ^ n) ^ 2) {w : Fin 4 → F} (hw : ∑ i, w i ^ (2 ^ n + 1) ≠ 0) :
    ∃ E : Subgroup (GL (Fin 4) F), E ≤ StatedSU 4 (2 ^ n) F ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 2 ∧
      ∀ g ∈ E, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ w = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  set σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 n with hσdef
  have hσ : IsUnitaryInvolution σ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  have hnorm : ∀ c : F, σ c * c = c ^ (2 ^ n + 1) := fun c => by
    rw [hσdef, CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_succ]
  obtain ⟨Z, hZp, hZcard, hZ⟩ := exists_torus_data hp hpq hF hnorm
  have hherm : herm σ w w = ∑ i, w i ^ (2 ^ n + 1) := by
    simp only [herm, hnorm]
  obtain ⟨c, hc⟩ := exists_smul_norm_one hσ (z := w) (by rw [hherm]; exact hw)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have he : herm σ (Pi.single 0 1 : Fin 4 → F) (Pi.single 0 1) = 1 := by
    simp [herm_single_left]
  obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_norm_one hσ (Or.inl le_rfl) he hc
  have hcard : Nat.card (↥Z × ↥Z) = p ^ 2 := by
    rw [Nat.card_prod, hZcard, sq]
  have hA : ∀ x : ↥Z × ↥Z, x ^ p = 1 := fun x => by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa using hZp _ x.1.2
    · simpa using hZp _ x.2.2
  obtain ⟨E, hEle, hE, hEc, hEfix⟩ := exists_stab_of_hom hA hcard (torusSU Z hZ)
    (torusSU_injective Z hZ) (v := Pi.single 0 1) (w := c • w)
    (torusSU_smul_single_zero Z hZ) t ht
  refine ⟨E, ?_, hE, hEc, fun g hg => ?_⟩
  · rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4]
    exact hEle
  · have h := hEfix g hg
    rw [Matrix.mulVec_smul] at h
    exact smul_right_injective _ hc0 h

theorem exists_stab_elemAbelian_ne_zero (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hF : Nat.card F = (2 ^ n) ^ 2) {w : Fin 4 → F} (hw : w ≠ 0) :
    ∃ E : Subgroup (GL (Fin 4) F), E ≤ StatedSU 4 (2 ^ n) F ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 1 ∧
      ∀ g ∈ E, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ w = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  set σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 n with hσdef
  have hσ : IsUnitaryInvolution σ :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  have hnorm : ∀ c : F, σ c * c = c ^ (2 ^ n + 1) := fun c => by
    rw [hσdef, CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_succ]
  obtain ⟨Z, hZp, hZcard, hZ⟩ := exists_torus_data hp hpq hF hnorm
  have hherm : herm σ w w = ∑ i, w i ^ (2 ^ n + 1) := by
    simp only [herm, hnorm]
  have hcard : Nat.card ↥Z = p ^ 1 := by rw [hZcard, pow_one]
  have hA : ∀ x : ↥Z, x ^ p = 1 := fun x => Subtype.ext (by simpa using hZp _ x.2)
  have hinj : Function.Injective ((torusSU Z hZ).comp (MonoidHom.inr ↥Z ↥Z)) :=
    (torusSU_injective Z hZ).comp (fun a b h => congrArg Prod.snd h)
  have hfinal : ∀ {E : Subgroup (GL (Fin 4) F)}, E ≤ SUid σ 4 → E ≤ StatedSU 4 (2 ^ n) F :=
    fun {E} h => by
      rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4]
      exact h
  by_cases hs : ∑ i, w i ^ (2 ^ n + 1) = 0
  ·
    obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
    set s : Fin 4 → F := ![1, u, 0, 0] with hsdef
    have hs0 : s ≠ 0 := fun h => by simpa [hsdef] using congrFun h 0
    have hss : herm σ s s = 0 := by
      simp only [herm, hsdef, Fin.sum_univ_four]
      simp
      linear_combination hu
    obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hσ (by norm_num) hs0 hss hw
      (by rw [hherm]; exact hs)
    obtain ⟨E, hEle, hE, hEc, hEfix⟩ := exists_stab_of_hom hA hcard
      ((torusSU Z hZ).comp (MonoidHom.inr ↥Z ↥Z)) hinj (v := s) (w := w)
      (fun x => torusSU_one_smul_eq Z hZ x (by simp [hsdef]) (by simp [hsdef])) t ht
    exact ⟨E, hfinal hEle, hE, hEc, hEfix⟩
  ·
    obtain ⟨c, hc⟩ := exists_smul_norm_one hσ (z := w) (by rw [hherm]; exact hs)
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc
    have he : herm σ (Pi.single 0 1 : Fin 4 → F) (Pi.single 0 1) = 1 := by
      simp [herm_single_left]
    obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_norm_one hσ (Or.inl le_rfl) he hc
    obtain ⟨E, hEle, hE, hEc, hEfix⟩ := exists_stab_of_hom hA hcard
      ((torusSU Z hZ).comp (MonoidHom.inr ↥Z ↥Z)) hinj (v := Pi.single 0 1) (w := c • w)
      (fun x => torusSU_one_smul_eq Z hZ x (by simp) (by simp)) t ht
    refine ⟨E, hfinal hEle, hE, hEc, fun g hg => ?_⟩
    have h := hEfix g hg
    rw [Matrix.mulVec_smul] at h
    exact smul_right_injective _ hc0 h

end Model

end CFSG.LocalAnalysis.RankThreeUC
