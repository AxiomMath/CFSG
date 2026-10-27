module

public import CFSG.HardMathSupport.U4FF.Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyClassifier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.EvenBN.U4
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family

variable {S : Type} [CommGroup S] [Finite S]

theorem eq_bot_of_normal_exponent_two (hS : ∀ s : S, s * s = 1) {X Y : Subgroup (MulAut S)}
    (hX : IsIrrOn X) (hn : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y)
    (hY : ∀ y ∈ Y, y * y = 1) : Y = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ x ∈ X, ∀ v ∈ fixV Y, x v ∈ fixV Y := by
    intro x hx v hv
    rw [mem_fixV] at hv ⊢
    intro y hy
    have h1 : x⁻¹ * y * x⁻¹⁻¹ ∈ Y := hn x⁻¹ (X.inv_mem hx) y hy
    have h2 : (x⁻¹ * y * x⁻¹⁻¹) v = v := hv _ h1
    have h3 : x⁻¹ (y (x v)) = v := by simpa [MulAut.mul_apply] using h2
    have h4 := congrArg x h3
    simpa using h4
  by_contra hne
  rcases hX (fixV Y) hinv with hF | hF
  ·
    have hS1 : Nontrivial S := by
      by_contra hS0
      rw [not_nontrivial_iff_subsingleton] at hS0
      apply hne
      rw [eq_bot_iff]
      intro y _
      rw [Subgroup.mem_bot]
      exact MulEquiv.ext fun s => Subsingleton.elim _ _
    have hPY : IsPGroup 2 Y := fun y => ⟨1, by
      apply Subtype.ext
      have : (y : MulAut S) * y = 1 := hY y y.2
      simpa [pow_two] using this⟩
    have hPS : IsPGroup 2 S := fun s => ⟨1, by simpa [pow_two] using hS s⟩
    have hmod := hPY.card_modEq_card_fixedPoints S
    have hfixcard : Nat.card (MulAction.fixedPoints Y S) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      have hone : ∀ v : MulAction.fixedPoints Y S, (v : S) = 1 := fun ⟨v, hv⟩ => by
        have hvF : v ∈ fixV Y := fun y hy => hv ⟨y, hy⟩
        rw [hF, Subgroup.mem_bot] at hvF
        exact hvF
      exact ⟨⟨fun a b => Subtype.ext ((hone a).trans (hone b).symm)⟩, ⟨⟨1, fun y => by simp⟩⟩⟩
    have h2 : 2 ∣ Nat.card S := by
      rcases hPS.card_eq_or_dvd with h1 | h1
      · exfalso
        rw [Nat.card_eq_one_iff_unique] at h1
        haveI := h1.1
        exact (not_subsingleton S) inferInstance
      · exact h1
    rw [hfixcard] at hmod
    have h3 : (1 : ℕ) ≡ 0 [MOD 2] := hmod.symm.trans ((Nat.modEq_zero_iff_dvd).2 h2)
    revert h3
    decide
  · apply hne
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun s => ?_
    have : s ∈ fixV Y := by rw [hF]; trivial
    exact this y hy

variable {n : ℕ} {L A : Subgroup (MulAut S)}

theorem sup_inf_centralizer_eq_bot (hS : ∀ s : S, s * s = 1) (hL : IsU4Group n L)
    (hA : IsElemAbelian2 A) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S)))
    (hirr : IsIrrOn (L ⊔ A)) : (L ⊔ A) ⊓ Subgroup.centralizer (L : Set (MulAut S)) = ⊥ := by
  classical
  obtain ⟨K, _, h, ⟨η⟩⟩ := exists_equiv_gramSU hL
  have hLC : L ⊓ Subgroup.centralizer (L : Set (MulAut S)) = ⊥ :=
    inf_centralizer_eq_bot_of_mulEquiv_gramSU h η
  have hLN : L ≤ Subgroup.normalizer (L : Set (MulAut S)) := Subgroup.le_normalizer
  have hXN : L ⊔ A ≤ Subgroup.normalizer (L : Set (MulAut S)) := sup_le hLN hAN
  refine eq_bot_of_normal_exponent_two hS hirr ?_ ?_
  · intro x hx y hy
    obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (L ⊔ A).mul_mem ((L ⊔ A).mul_mem hx hyX) ((L ⊔ A).inv_mem hx)
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hxn : x ∈ Subgroup.normalizer (L : Set (MulAut S)) := hXN hx
      have hl' : x⁻¹ * l * x ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxn) l).mp hl
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hyC _ hl'
      calc l * (x * y * x⁻¹) = x * ((x⁻¹ * l * x) * y) * x⁻¹ := by group
        _ = x * (y * (x⁻¹ * l * x)) * x⁻¹ := by rw [hc]
        _ = (x * y * x⁻¹) * l := by group
  · intro y hy
    obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨l, hl, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_normalizer hAN hyX
    have hcomm : ∀ l' ∈ L, a * l' * a⁻¹ = l⁻¹ * l' * l := by
      intro l' hl'
      have hc := Subgroup.mem_centralizer_iff.mp hyC l' hl'
      calc a * l' * a⁻¹ = l⁻¹ * ((l * a) * l') * a⁻¹ := by group
        _ = l⁻¹ * (l' * (l * a)) * a⁻¹ := by rw [← hc]
        _ = l⁻¹ * l' * l := by group
    have ha2 : a * a = 1 := by simpa [sq] using hA.2 a ha
    have hl2 : l * l = 1 := by
      have hc : l * l ∈ Subgroup.centralizer (L : Set (MulAut S)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l' hl'
        have e1 : a * l' * a⁻¹ = l⁻¹ * l' * l := hcomm l' hl'
        have hl'' : l⁻¹ * l' * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hl') hl
        have e2 : a * (l⁻¹ * l' * l) * a⁻¹ = l⁻¹ * (l⁻¹ * l' * l) * l := hcomm _ hl''
        have e3 : a * (a * l' * a⁻¹) * a⁻¹ = l' := by
          calc a * (a * l' * a⁻¹) * a⁻¹ = (a * a) * l' * (a * a)⁻¹ := by group
            _ = l' := by rw [ha2]; group
        rw [e1, e2] at e3
        calc l' * (l * l) = l * l * (l⁻¹ * (l⁻¹ * l' * l) * l) := by group
          _ = l * l * l' := by rw [e3]
      have hmem : l * l ∈ L ⊓ Subgroup.centralizer (L : Set (MulAut S)) := ⟨L.mul_mem hl hl, hc⟩
      rw [hLC, Subgroup.mem_bot] at hmem
      exact hmem
    calc (l * a) * (l * a) = l * (a * l * a⁻¹) * (a * a) := by group
      _ = l * (l⁻¹ * l * l) * 1 := by rw [hcomm l hl, ha2]
      _ = l * l := by group
      _ = 1 := hl2

theorem mem_of_fieldFactor_eq_one (hS : ∀ s : S, s * s = 1) (hL : IsU4Group n L)
    (hA : IsElemAbelian2 A) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S)))
    (hirr : IsIrrOn (L ⊔ A)) {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    (η : ↥L ≃* gramSU h (miyamotoJ4 K)) {a : MulAut S} (ha : a ∈ A)
    (h1 : miyamotoFieldFactorG h L η ⟨a, hAN ha⟩ = 1) : a ∈ L := by
  have hC := sup_inf_centralizer_eq_bot hS hL hA hAN hirr
  obtain ⟨l, hl, c, hc, hlc⟩ := (miyamotoFieldFactorG_eq_one_iff h L η _).1 h1
  have hcX : c ∈ L ⊔ A := by
    have e : c = l⁻¹ * a := by
      have hlc' : a = l * c := hlc
      rw [hlc']; group
    rw [e]
    exact (L ⊔ A).mul_mem ((L ⊔ A).inv_mem (Subgroup.mem_sup_left hl)) (Subgroup.mem_sup_right ha)
  have hc1 : c = 1 := by
    have : c ∈ (L ⊔ A) ⊓ Subgroup.centralizer (L : Set (MulAut S)) := ⟨hcX, hc⟩
    rw [hC, Subgroup.mem_bot] at this
    exact this
  have hlc' : a = l * c := hlc
  rw [hlc', hc1, mul_one]
  exact hl

theorem card_le_two_mul_inf (hS : ∀ s : S, s * s = 1) (hL : IsU4Group n L)
    (hA : IsElemAbelian2 A) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S)))
    (hirr : IsIrrOn (L ⊔ A)) : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) := by
  classical
  obtain ⟨K, _, h, ⟨η⟩⟩ := exists_equiv_gramSU hL
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : A →* (K ≃+* K) := (miyamotoFieldFactorG h L η).comp (Subgroup.inclusion hAN)
  have hrange : Nat.card φ.range ≤ 2 := by
    refine CFSG.QuasithinUnique.Setup.X5.card_le_two_of_sq_eq_one φ.range ?_
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (hA.2 a a.2)
    rw [this, map_one]
  have hmem : ∀ a : φ.ker, ((a : A) : MulAut S) ∈ A ⊓ L := fun a =>
    ⟨(a : A).2, mem_of_fieldFactor_eq_one hS hL hA hAN hirr h η (a : A).2 a.2⟩
  have hker : Nat.card φ.ker ≤ Nat.card ↥(A ⊓ L) := by
    refine Nat.card_le_card_of_injective
      (fun a : φ.ker => (⟨((a : A) : MulAut S), hmem a⟩ : ↥(A ⊓ L))) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa using this
  have h1 := Subgroup.card_ker_mul_card_range φ
  calc Nat.card A = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ Nat.card ↥(A ⊓ L) * 2 := Nat.mul_le_mul hker hrange
    _ = 2 * Nat.card ↥(A ⊓ L) := mul_comm _ _

theorem inv_mul_mem_of_not_mem (hS : ∀ s : S, s * s = 1) (hL : IsU4Group n L)
    (hA : IsElemAbelian2 A) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S)))
    (hirr : IsIrrOn (L ⊔ A)) {a a' : MulAut S} (ha : a ∈ A) (ha' : a' ∈ A) (haL : a ∉ L)
    (ha'L : a' ∉ L) : a⁻¹ * a' ∈ L := by
  classical
  obtain ⟨K, _, h, ⟨η⟩⟩ := exists_equiv_gramSU hL
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : A →* (K ≃+* K) := (miyamotoFieldFactorG h L η).comp (Subgroup.inclusion hAN)
  have hrange : Nat.card φ.range ≤ 2 := by
    refine CFSG.QuasithinUnique.Setup.X5.card_le_two_of_sq_eq_one φ.range ?_
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (hA.2 x x.2)
    rw [this, map_one]
  have hφa : φ ⟨a, ha⟩ ≠ 1 := fun h1 => haL (mem_of_fieldFactor_eq_one hS hL hA hAN hirr h η ha h1)
  have hφa' : φ ⟨a', ha'⟩ ≠ 1 := fun h1 =>
    ha'L (mem_of_fieldFactor_eq_one hS hL hA hAN hirr h η ha' h1)
  have heq : φ ⟨a, ha⟩ = φ ⟨a', ha'⟩ := by
    by_contra hne
    haveI : Finite φ.range := Finite.of_injective (fun x : φ.range => (x : K ≃+* K))
      Subtype.val_injective
    let f : Fin 3 → φ.range :=
      ![⟨1, one_mem _⟩, ⟨φ ⟨a, ha⟩, ⟨_, rfl⟩⟩, ⟨φ ⟨a', ha'⟩, ⟨_, rfl⟩⟩]
    haveI : Fintype φ.range := Fintype.ofFinite _
    have hlt : Fintype.card φ.range < Fintype.card (Fin 3) := by
      rw [← Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
    fin_cases i <;> fin_cases j <;> simp [f, Subtype.ext_iff] at hij hfij <;>
      first
        | exact hφa hfij.symm
        | exact hφa hfij
        | exact hφa' hfij.symm
        | exact hφa' hfij
        | exact hne hfij
        | exact hne hfij.symm
  have h1 : φ ⟨a⁻¹ * a', A.mul_mem (A.inv_mem ha) ha'⟩ = 1 := by
    have : (⟨a⁻¹ * a', A.mul_mem (A.inv_mem ha) ha'⟩ : A) = ⟨a, ha⟩⁻¹ * ⟨a', ha'⟩ := rfl
    rw [this, map_mul, map_inv, heq, inv_mul_cancel]
  exact mem_of_fieldFactor_eq_one hS hL hA hAN hirr h η (A.mul_mem (A.inv_mem ha) ha') h1

end CFSG.HardMathSupport.U4FF
