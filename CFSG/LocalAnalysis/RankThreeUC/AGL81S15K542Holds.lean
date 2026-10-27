module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Clause
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.U33Clause
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.Harris.Interfaces
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Bridge
public import CFSG.Quasithin.H13.J4Classes

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K542Proof

open Module

section Schur

variable {H : Type} [Group H] {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]

@[expose] noncomputable def commOf (π : H →* Module.End (ZMod 2) Q) :
    Subalgebra (ZMod 2) (Module.End (ZMod 2) Q) :=
  Subalgebra.centralizer (ZMod 2) (Set.range π)

theorem mem_commOf {π : H →* Module.End (ZMod 2) Q} {ψ : Module.End (ZMod 2) Q} :
    ψ ∈ commOf π ↔ ∀ h, π h * ψ = ψ * π h := by
  simp only [commOf, Subalgebra.mem_centralizer_iff, Set.forall_mem_range]

@[expose] def IrrOn (π : H →* Module.End (ZMod 2) Q) : Prop :=
  ∀ Z : Submodule (ZMod 2) Q, (∀ h, ∀ z ∈ Z, π h z ∈ Z) → Z = ⊥ ∨ Z = ⊤

theorem commOf_injective {π : H →* Module.End (ZMod 2) Q} (hirr : IrrOn π)
    {ψ : Module.End (ZMod 2) Q} (hψ : ψ ∈ commOf π) (h0 : ψ ≠ 0) : Function.Injective ψ := by
  have hinv : ∀ h, ∀ z ∈ LinearMap.ker ψ, π h z ∈ LinearMap.ker ψ := by
    intro h z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have := congrArg (fun φ : Module.End (ZMod 2) Q => φ z) ((mem_commOf.mp hψ) h)
    simp only [Module.End.mul_apply] at this
    rw [hz, map_zero] at this
    exact this.symm
  rcases hirr _ hinv with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exfalso
    apply h0
    ext v
    have hv : v ∈ LinearMap.ker ψ := by rw [h]; exact Submodule.mem_top
    simpa using hv

theorem commOf_isField [Finite Q] [Nontrivial Q] {π : H →* Module.End (ZMod 2) Q}
    (hirr : IrrOn π) : IsField (commOf π) := by
  have : Finite (Module.End (ZMod 2) Q) :=
    Finite.of_injective (fun φ : Module.End (ZMod 2) Q => (φ : Q → Q))
      (fun a b h => LinearMap.ext fun v => congrFun h v)
  have : Nontrivial (commOf π) :=
    ⟨⟨1, Subalgebra.one_mem _⟩, ⟨0, Subalgebra.zero_mem _⟩,
      fun h => one_ne_zero (congrArg Subtype.val h)⟩
  have : NoZeroDivisors (commOf π) :=
    ⟨fun {a b} hab => by
      by_cases ha : (a : Module.End (ZMod 2) Q) = 0
      · exact Or.inl (Subtype.ext ha)
      · refine Or.inr (Subtype.ext ?_)
        have hab' : (a : Module.End (ZMod 2) Q) * (b : Module.End (ZMod 2) Q) = 0 := by
          simpa using congrArg Subtype.val hab
        apply LinearMap.ext
        intro v
        apply commOf_injective hirr a.2 ha
        have h := congrArg (fun φ : Module.End (ZMod 2) Q => φ v) hab'
        simpa [Module.End.mul_apply] using h⟩
  have : IsDomain (commOf π) := NoZeroDivisors.to_isDomain _
  exact Finite.isDomain_to_isField _

end Schur

section Linear

theorem perfect_hom_eq_one {G M : Type*} [Group G] [Group.IsPerfect G] [CommMonoid M]
    (f : G →* M) (g : G) : f g = 1 := by
  have h := Abelianization.commutator_subset_ker f.toHomUnits
  rw [Group.IsPerfect.commutator_eq_top] at h
  have hg : f.toHomUnits g = 1 := h (Subgroup.mem_top g)
  rw [← MonoidHom.coe_toHomUnits, hg, Units.val_one]

theorem exists_sl_embedding {E : Type} [Field E] {Q : Type} [AddCommGroup Q] [Module E Q]
    [Module.Finite E Q] {H : Type} [Group H] [Group.IsPerfect H] (g : H →* Module.End E Q)
    (hg : Function.Injective g) :
    ∃ s : H →* Matrix.SpecialLinearGroup (Fin (finrank E Q)) E, Function.Injective s := by
  let b := Module.finBasisOfFinrankEq E Q (rfl : finrank E Q = finrank E Q)
  let ρ : H →* Matrix.GeneralLinearGroup (Fin (finrank E Q)) E :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp g.toHomUnits
  have hdet : ∀ h, ((ρ h : Matrix.GeneralLinearGroup (Fin (finrank E Q)) E) :
      Matrix (Fin (finrank E Q)) (Fin (finrank E Q)) E).det = 1 := by
    intro h
    have := perfect_hom_eq_one (Matrix.GeneralLinearGroup.det.comp ρ) h
    simpa using congrArg Units.val this
  let s : H →* Matrix.SpecialLinearGroup (Fin (finrank E Q)) E :=
    { toFun := fun h => ⟨(ρ h : Matrix (Fin (finrank E Q)) (Fin (finrank E Q)) E), hdet h⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp; rfl) }
  refine ⟨s, fun a a' haa => ?_⟩
  have h1 : (ρ a : Matrix (Fin (finrank E Q)) (Fin (finrank E Q)) E) = ρ a' :=
    congrArg Subtype.val haa
  have h3 : (LinearMap.toMatrixAlgEquiv b) (g a) = (LinearMap.toMatrixAlgEquiv b) (g a') := by
    simpa [ρ] using h1
  exact hg ((LinearMap.toMatrixAlgEquiv b).injective h3)

theorem card_sl_two_pow {E : Type} [Field E] [Finite E] {k : ℕ} (hE : Nat.card E = 2 ^ k)
    (d : ℕ) [NeZero d] :
    Nat.card (Matrix.SpecialLinearGroup (Fin d) E) =
      (∏ i : Fin d, ((2 ^ k) ^ d - (2 ^ k) ^ (i : ℕ))) / (2 ^ k - 1) := by
  have : Fintype E := Fintype.ofFinite E
  have hq : Fintype.card E = 2 ^ k := by rw [← Nat.card_eq_fintype_card]; exact hE
  rw [Matrix.card_SL_field d, hq]

theorem card_sl_values {E : Type} [Field E] [Finite E] {k d : ℕ} (hE : Nat.card E = 2 ^ k) :
    (k = 2 ∧ d = 2 → Nat.card (Matrix.SpecialLinearGroup (Fin d) E) = 60) ∧
    (k = 4 ∧ d = 1 → Nat.card (Matrix.SpecialLinearGroup (Fin d) E) = 1) ∧
    (k = 2 ∧ d = 3 → Nat.card (Matrix.SpecialLinearGroup (Fin d) E) = 60480) ∧
    (k = 3 ∧ d = 2 → Nat.card (Matrix.SpecialLinearGroup (Fin d) E) = 504) ∧
    (k = 6 ∧ d = 1 → Nat.card (Matrix.SpecialLinearGroup (Fin d) E) = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rintro ⟨rfl, rfl⟩ <;>
    (rw [card_sl_two_pow hE]; simp [Fin.prod_univ_succ])

theorem no_sl3_embedding {E : Type} [Field E] [Finite E] {H : Type} [Group H]
    (hE : Nat.card E = 2 ^ 2) (hH : Nat.card H = 6048)
    (hZ : ∀ h : H, (∀ h', h * h' = h' * h) → h = 1)
    (s : H →* Matrix.SpecialLinearGroup (Fin 3) E) (hs : Function.Injective s) : False := by
  have hunits : Nat.card Eˣ = 3 := by rw [Nat.card_units, hE]; norm_num
  have hc3 : ∀ c : Eˣ, c ^ 3 = 1 := fun c => by rw [← hunits]; exact pow_card_eq_one'
  let σ : Eˣ →* Matrix.SpecialLinearGroup (Fin 3) E :=
    { toFun := fun c => ⟨Matrix.scalar (Fin 3) (c : E), by
        have h := congrArg Units.val (hc3 c)
        simp only [Units.val_pow_eq_pow_val, Units.val_one] at h
        simp [Matrix.scalar_apply, Matrix.det_diagonal, h]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show Matrix.scalar (Fin 3) ((a * b : Eˣ) : E) =
          Matrix.scalar (Fin 3) (a : E) * Matrix.scalar (Fin 3) (b : E)
        rw [Units.val_mul, map_mul]) }
  have hσ : ∀ c : Eˣ, ((σ c : Matrix.SpecialLinearGroup (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E) = Matrix.scalar (Fin 3) (c : E) := fun c => rfl
  have hcomm : ∀ (h : H) (c : Eˣ), Commute (s h) (σ c) := by
    intro h c
    apply Subtype.ext
    show (s h : Matrix (Fin 3) (Fin 3) E) * (σ c : Matrix (Fin 3) (Fin 3) E) =
      (σ c : Matrix (Fin 3) (Fin 3) E) * (s h : Matrix (Fin 3) (Fin 3) E)
    rw [hσ]
    exact ((Matrix.scalar_commute (c : E) (fun r => mul_comm _ _) _)).symm
  let f : H × Eˣ →* Matrix.SpecialLinearGroup (Fin 3) E := MonoidHom.noncommCoprod s σ hcomm
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨h, c⟩ hhc
    rw [MonoidHom.noncommCoprod_apply] at hhc
    have h1 : s h = σ c⁻¹ := by
      rw [map_inv]; exact eq_inv_of_mul_eq_one_left hhc
    have h2 : ∀ h', h * h' = h' * h := by
      intro h'
      apply hs
      rw [map_mul, map_mul, h1]
      exact (hcomm h' c⁻¹).eq.symm
    have h3 : h = 1 := hZ h h2
    subst h3
    rw [map_one, one_mul] at hhc
    have h4 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) E =>
      (A : Matrix (Fin 3) (Fin 3) E) 0 0) hhc
    simp only [hσ, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h4
    have h5 : c = 1 := Units.ext (by simpa using h4)
    rw [h5]; rfl
  have hdvd := Subgroup.card_dvd_of_injective f hf
  rw [Nat.card_prod, hH, hunits, (card_sl_values (d := 3) hE).2.2.1 ⟨rfl, rfl⟩] at hdvd
  norm_num at hdvd

theorem no_sl_embedding {E : Type} [Field E] [Finite E] {H : Type} [Group H] {n k d : ℕ}
    (hk : 2 ≤ k) (hd : 1 ≤ d) (hkd : k * d = n) (hE : Nat.card E = 2 ^ k)
    (hcard : (n = 4 ∧ Nat.card H = 360) ∨ (n = 6 ∧ Nat.card H = 6048))
    (hZ : ∀ h : H, (∀ h', h * h' = h' * h) → h = 1)
    (s : H →* Matrix.SpecialLinearGroup (Fin d) E) (hs : Function.Injective s) : False := by
  have hdvd : Nat.card H ∣ Nat.card (Matrix.SpecialLinearGroup (Fin d) E) :=
    Subgroup.card_dvd_of_injective s hs
  have hv := card_sl_values (d := d) hE
  have hkle : k ≤ n := by nlinarith
  rcases hcard with ⟨hn, hH⟩ | ⟨hn, hH⟩
  · subst hn
    interval_cases k
    · have hd2 : d = 2 := by omega
      rw [hH, hv.1 ⟨rfl, hd2⟩] at hdvd
      norm_num at hdvd
    · omega
    · have hd1 : d = 1 := by omega
      rw [hH, hv.2.1 ⟨rfl, hd1⟩] at hdvd
      norm_num at hdvd
  · subst hn
    interval_cases k
    · have hd3 : d = 3 := by omega
      subst hd3
      exact no_sl3_embedding hE hH hZ s hs
    · have hd2 : d = 2 := by omega
      rw [hH, hv.2.2.2.1 ⟨rfl, hd2⟩] at hdvd
      norm_num at hdvd
    · omega
    · omega
    · have hd1 : d = 1 := by omega
      rw [hH, hv.2.2.2.2 ⟨rfl, hd1⟩] at hdvd
      norm_num at hdvd

end Linear

section Endo

variable {H : Type} [Group H] {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]

theorem endo_zero_or_one [Finite Q] {n : ℕ} (hQ : Nat.card Q = 2 ^ n) (hn : 2 ≤ n)
    [Group.IsPerfect H] (hZ : ∀ h : H, (∀ h', h * h' = h' * h) → h = 1)
    (hcard : (n = 4 ∧ Nat.card H = 360) ∨ (n = 6 ∧ Nat.card H = 6048))
    {π : H →* Module.End (ZMod 2) Q} (hirr : IrrOn π) (hinj : Function.Injective π)
    {ξ : Module.End (ZMod 2) Q} (hξ : ξ ∈ commOf π) : ξ = 0 ∨ ξ = 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1⟩ := hcon
  have hQnt : Nontrivial Q := by
    rw [← Finite.one_lt_card_iff_nontrivial, hQ]
    exact Nat.one_lt_two_pow_iff.mpr (by omega)
  have : Finite (Module.End (ZMod 2) Q) :=
    Finite.of_injective (fun φ : Module.End (ZMod 2) Q => (φ : Q → Q))
      (fun a b h => LinearMap.ext fun v => congrFun h v)
  letI : Field (commOf π) := (commOf_isField hirr).toField
  have hEfin : Finite (commOf π) := inferInstance
  have : Module.Finite (commOf π) Q := Module.Finite.of_finite
  have hEcard : Nat.card (commOf π) = 2 ^ finrank (ZMod 2) (commOf π) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := commOf π), Nat.card_zmod]
  have hQE : Nat.card Q = Nat.card (commOf π) ^ finrank (commOf π) Q :=
    Module.natCard_eq_pow_finrank (K := commOf π) (V := Q)
  obtain ⟨k, hk⟩ : ∃ k, k = finrank (ZMod 2) (commOf π) := ⟨_, rfl⟩
  rw [← hk] at hEcard
  rw [hQ, hEcard, ← pow_mul] at hQE
  have hkd : n = k * finrank (commOf π) Q := Nat.pow_right_injective (le_refl 2) hQE
  have hne01 : (0 : commOf π) ≠ 1 := zero_ne_one
  have hne0 : (0 : commOf π) ≠ ⟨ξ, hξ⟩ := fun h => h0 (by simpa using (congrArg Subtype.val h).symm)
  have hne1 : (1 : commOf π) ≠ ⟨ξ, hξ⟩ := fun h => h1 (by simpa using (congrArg Subtype.val h).symm)
  have h3 : 3 ≤ Nat.card (commOf π) := by
    classical
    haveI := Fintype.ofFinite (commOf π)
    rw [Nat.card_eq_fintype_card]
    have hc : ({0, 1, ⟨ξ, hξ⟩} : Finset (commOf π)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using hne1
      · simp [hne01, hne0]
    calc 3 = _ := hc.symm
      _ ≤ _ := Finset.card_le_univ _
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    rw [hEcard] at h3
    interval_cases k <;> norm_num at h3
  have hd1 : 1 ≤ finrank (commOf π) Q := by
    rcases Nat.eq_zero_or_pos (finrank (commOf π) Q) with hd0 | hd0
    · rw [hd0, mul_zero] at hkd; omega
    · exact hd0
  let g : H →* Module.End (commOf π) Q :=
    { toFun := fun h =>
        { toFun := fun q => π h q
          map_add' := fun a b => map_add _ a b
          map_smul' := fun e q => by
            show π h (e.1 q) = e.1 (π h q)
            exact congrArg (fun φ : Module.End (ZMod 2) Q => φ q) ((mem_commOf.mp e.2) h) }
      map_one' := LinearMap.ext fun q => by simp
      map_mul' := fun a b => LinearMap.ext fun q => by simp }
  have hg : Function.Injective g := fun a b hab =>
    hinj (LinearMap.ext fun q => congrArg (fun φ : Module.End (commOf π) Q => φ q) hab)
  obtain ⟨s, hs⟩ := exists_sl_embedding g hg
  exact no_sl_embedding hk2 hd1 hkd.symm hEcard hcard hZ s hs

end Endo

section Sec

variable {H : Type} [Group H] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

abbrev subq (U C : Submodule (ZMod 2) W) : Submodule (ZMod 2) ↥U := C.comap U.subtype

@[expose] noncomputable def secMap (U C : Submodule (ZMod 2) W) (f : Module.End (ZMod 2) W)
    (hU : ∀ u ∈ U, f u ∈ U) (hC : ∀ c ∈ C, f c ∈ C) :
    Module.End (ZMod 2) (↥U ⧸ subq U C) :=
  Submodule.mapQ (subq U C) (subq U C) (f.restrict hU) (fun u hu => hC u hu)

@[expose] noncomputable def secRep (π : H →* Module.End (ZMod 2) W) (U C : Submodule (ZMod 2) W)
    (hU : ∀ h, ∀ u ∈ U, π h u ∈ U) (hC : ∀ h, ∀ c ∈ C, π h c ∈ C) :
    H →* Module.End (ZMod 2) (↥U ⧸ subq U C) where
  toFun h := secMap U C (π h) (hU h) (hC h)
  map_one' := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H u =>
      show (Submodule.Quotient.mk (⟨π 1 u, hU 1 u u.2⟩ : ↥U) : ↥U ⧸ subq U C) =
        Submodule.Quotient.mk u
      congr 1
      apply Subtype.ext
      simp
  map_mul' a b := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H u =>
      show (Submodule.Quotient.mk (⟨π (a * b) u, hU (a * b) u u.2⟩ : ↥U) : ↥U ⧸ subq U C) =
        Submodule.Quotient.mk ⟨π a (π b u), hU a _ (hU b u u.2)⟩
      congr 1
      apply Subtype.ext
      simp

theorem secRep_apply (π : H →* Module.End (ZMod 2) W) (U C : Submodule (ZMod 2) W)
    (hU : ∀ h, ∀ u ∈ U, π h u ∈ U) (hC : ∀ h, ∀ c ∈ C, π h c ∈ C) (h : H) (u : ↥U) :
    secRep π U C hU hC h (Submodule.Quotient.mk u) = Submodule.Quotient.mk ⟨π h u, hU h u u.2⟩ :=
  rfl

open scoped commutatorElement in
theorem isPerfect_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) ⊤).eq_bot_or_eq_top with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hm : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [commutator_def, hb, Subgroup.mem_bot] at hm
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hm)
  · rw [commutator_def]
    exact ht

theorem center_trivial_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) (g : G) (hg : ∀ g', g * g' = g' * g) : g = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · have : g ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g' => (hg g').symm
    rw [hb, Subgroup.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have : a ∈ Subgroup.center G := ht ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem finrank_sec [Finite W] (U C : Submodule (ZMod 2) W) (hCU : C ≤ U) :
    finrank (ZMod 2) (↥U ⧸ subq U C) + finrank (ZMod 2) C = finrank (ZMod 2) U := by
  have h := Submodule.finrank_quotient_add_finrank (subq U C)
  rw [(Submodule.comapSubtypeEquivOfLe hCU).finrank_eq] at h
  exact h

theorem irrOn_sec (π : H →* Module.End (ZMod 2) W) (U C : Submodule (ZMod 2) W)
    (hCU : C ≤ U) (hU : ∀ h, ∀ u ∈ U, π h u ∈ U) (hC : ∀ h, ∀ c ∈ C, π h c ∈ C)
    (hirr : ∀ Z : Submodule (ZMod 2) W, (∀ h, ∀ z ∈ Z, π h z ∈ Z) → C ≤ Z → Z ≤ U →
      Z = C ∨ Z = U) :
    IrrOn (secRep π U C hU hC) := by
  intro Zb hZb
  set Z : Submodule (ZMod 2) W := (Zb.comap (subq U C).mkQ).map U.subtype with hZdef
  have hZmem : ∀ w, w ∈ Z ↔ ∃ u : ↥U, (u : W) = w ∧
      (Submodule.Quotient.mk u : ↥U ⧸ subq U C) ∈ Zb := by
    intro w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, rfl, hu⟩
    · rintro ⟨u, rfl, hu⟩
      exact ⟨u, hu, rfl⟩
  have hinv : ∀ h, ∀ z ∈ Z, π h z ∈ Z := by
    intro h z hz
    obtain ⟨u, rfl, hu⟩ := (hZmem z).1 hz
    refine (hZmem _).2 ⟨⟨π h u, hU h u u.2⟩, rfl, ?_⟩
    have := hZb h _ hu
    rwa [secRep_apply] at this
  have hCZ : C ≤ Z := by
    intro c hc
    refine (hZmem c).2 ⟨⟨c, hCU hc⟩, rfl, ?_⟩
    have : (Submodule.Quotient.mk ⟨c, hCU hc⟩ : ↥U ⧸ subq U C) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hc
    rw [this]
    exact Zb.zero_mem
  have hZU : Z ≤ U := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  rcases hirr Z hinv hCZ hZU with h | h
  · left
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have : (u : W) ∈ Z := (hZmem _).2 ⟨u, rfl, hq⟩
    rw [h] at this
    rw [Submodule.mem_bot]
    exact (Submodule.Quotient.mk_eq_zero _).2 this
  · right
    rw [eq_top_iff]
    intro q _
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have : (u : W) ∈ Z := by rw [h]; exact u.2
    obtain ⟨u', hu', hu'Z⟩ := (hZmem _).1 this
    have : u' = u := Subtype.ext hu'
    rw [← this]
    exact hu'Z

theorem endo_rel [Finite W] [IsSimpleGroup H] (hnab : ∃ a b : H, a * b ≠ b * a) {n : ℕ}
    (hn : 2 ≤ n) (hcard : (n = 4 ∧ Nat.card H = 360) ∨ (n = 6 ∧ Nat.card H = 6048))
    (π : H →* Module.End (ZMod 2) W) (ξ : Module.End (ZMod 2) W) (U C : Submodule (ZMod 2) W)
    (hCU : C ≤ U) (hU : ∀ h, ∀ u ∈ U, π h u ∈ U) (hC : ∀ h, ∀ c ∈ C, π h c ∈ C)
    (hξU : ∀ u ∈ U, ξ u ∈ U) (hξC : ∀ c ∈ C, ξ c ∈ C) (hcomm : ∀ h w, π h (ξ w) = ξ (π h w))
    (hirr : ∀ Z : Submodule (ZMod 2) W, (∀ h, ∀ z ∈ Z, π h z ∈ Z) → C ≤ Z → Z ≤ U →
      Z = C ∨ Z = U)
    (hdim : finrank (ZMod 2) U = finrank (ZMod 2) C + n) (hξinj : ∀ u ∈ U, ξ u ∈ C → u ∈ C) :
    ∀ u ∈ U, ξ u - u ∈ C := by
  classical
  have hdimQ : finrank (ZMod 2) (↥U ⧸ subq U C) = n := by
    have := finrank_sec U C hCU
    omega
  have hQcard : Nat.card (↥U ⧸ subq U C) = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdimQ]
  have hirrQ := irrOn_sec π U C hCU hU hC hirr
  have hQnt : Nontrivial (↥U ⧸ subq U C) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hQcard]
    exact Nat.one_lt_two_pow_iff.mpr (by omega)
  have hinjQ : Function.Injective (secRep π U C hU hC) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (secRep π U C hU hC).ker with hb | ht
    · exact hb
    · exfalso
      obtain ⟨q, hq⟩ := exists_ne (0 : ↥U ⧸ subq U C)
      have hker : ∀ h, secRep π U C hU hC h = 1 := fun h =>
        MonoidHom.mem_ker.mp (ht ▸ Subgroup.mem_top h)
      rcases hirrQ (Submodule.span (ZMod 2) {q}) (fun h z hz => by
          rw [hker h]; exact hz) with hs | hs
      · exact hq (by
          have : q ∈ Submodule.span (ZMod 2) {q} := Submodule.mem_span_singleton_self q
          rw [hs, Submodule.mem_bot] at this
          exact this)
      · have h1 := congrArg (fun S : Submodule (ZMod 2) (↥U ⧸ subq U C) => finrank (ZMod 2) S) hs
        simp only [finrank_span_singleton hq, finrank_top] at h1
        omega
  have hcommQ : secMap U C ξ hξU hξC ∈ commOf (secRep π U C hU hC) := by
    refine mem_commOf.mpr fun h => ?_
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H u =>
      show (Submodule.Quotient.mk (⟨π h (ξ u), hU h _ (hξU u u.2)⟩ : ↥U) : ↥U ⧸ subq U C) =
        Submodule.Quotient.mk ⟨ξ (π h u), hξU _ (hU h u u.2)⟩
      congr 1
      exact Subtype.ext (hcomm h u)
  haveI := isPerfect_of_simple hnab
  rcases endo_zero_or_one hQcard hn (center_trivial_of_simple hnab) hcard hirrQ hinjQ hcommQ with
    h | h
  · exfalso
    obtain ⟨q, hq⟩ := exists_ne (0 : ↥U ⧸ subq U C)
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine hq ?_
    have := congrArg (fun φ : Module.End (ZMod 2) (↥U ⧸ subq U C) => φ (Submodule.Quotient.mk u)) h
    have h2 : ξ u ∈ C := (Submodule.Quotient.mk_eq_zero (subq U C)).1 this
    exact (Submodule.Quotient.mk_eq_zero (subq U C)).2 (hξinj u u.2 h2)
  · intro u hu
    have := congrArg (fun φ : Module.End (ZMod 2) (↥U ⧸ subq U C) =>
      φ (Submodule.Quotient.mk ⟨u, hu⟩)) h
    exact (Submodule.Quotient.eq (subq U C)).1 this

end Sec

section Glue

open CFSG.Quasithin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.RankThree.FFModules CFSG.AGLEmbedding

variable {X : Type} [Group X] {T : Subgroup X} (hV : CFSG.Open.IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem clause_to_module [Finite X] (L : Subgroup (X ⧸ gnC T)) {n : ℕ}
    (hHI : HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T))
    (hrel : (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
          Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
        ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ n) :
    (∀ Z : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV)), CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (gnRep hV) L Z →
      fixOn (gnRep hV) L (commOn (gnRep hV) L ⊤) ≤ Z → Z ≤ commOn (gnRep hV) L ⊤ →
      Z = fixOn (gnRep hV) L (commOn (gnRep hV) L ⊤) ∨ Z = commOn (gnRep hV) L ⊤) ∧
    Module.finrank (ZMod 2) ↥(commOn (gnRep hV) L ⊤) =
      Module.finrank (ZMod 2) ↥(fixOn (gnRep hV) L (commOn (gnRep hV) L ⊤)) + n := by
  classical
  set ρ := gnRep hV with hρ
  set L' := L.comap (QuotientGroup.mk' (gnC T)) with hL'
  set U := commOn ρ L ⊤ with hU
  set C := fixOn ρ L U with hC
  have hUs : subOf hV U = ⁅gnV T, L'⁆ := subOf_commOn hV L
  have hCs : subOf hV C = ⁅gnV T, L'⁆ ⊓ Subgroup.centralizer (L' : Set X) := by
    rw [hC, subOf_fixOn, hUs]
  have hCU : C ≤ U := fun v hv => (mem_fixOn.mp hv).1
  have hcard : ∀ N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV)),
      Nat.card N = 2 ^ Module.finrank (ZMod 2) N := by
    intro N
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  refine ⟨fun Z hZinv hCZ hZU => ?_, ?_⟩
  · have hW1 : ⁅gnV T, L'⁆ ⊓ Subgroup.centralizer (L' : Set X) ≤ subOf hV Z := by
      rw [← hCs]; exact (subOf_le_subOf_iff hV).mpr hCZ
    have hW2 : subOf hV Z ≤ ⁅gnV T, L'⁆ := by
      rw [← hUs]; exact (subOf_le_subOf_iff hV).mpr hZU
    have key : ∀ g ∈ L', ∀ h ∈ subOf hV Z, g * h * g⁻¹ ∈ subOf hV Z := by
      rintro g hg _ ⟨w, hw, rfl⟩
      rw [← elt_gnRep]
      exact ⟨_, hZinv (QuotientGroup.mk g) hg w hw, rfl⟩
    have hW3 : L' ≤ Subgroup.normalizer (subOf hV Z : Set X) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨key g hg h, fun hh => ?_⟩
      have := key g⁻¹ (L'.inv_mem hg) _ hh
      have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rwa [e] at this
    have back : ∀ Z' : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV)),
        subOf hV Z = subOf hV Z' → Z = Z' := fun Z' h => by
      rw [← modOf_subOf hV Z, ← modOf_subOf hV Z', h]
    rcases hHI.2 (subOf hV Z) hW1 hW2 hW3 with h | h
    · exact Or.inl (back C (h.trans hCs.symm))
    · exact Or.inr (back U (h.trans hUs.symm))
  · have hle : subOf hV C ≤ subOf hV U := (subOf_le_subOf_iff hV).mpr hCU
    rw [← hCs, ← hUs] at hrel
    have h1 := Subgroup.relIndex_mul_card (subOf hV C) (subOf hV U)
    rw [inf_eq_left.mpr hle, card_subOf, card_subOf, hcard, hcard, hrel, ← pow_add] at h1
    have h2 := Nat.pow_right_injective (le_refl 2) h1
    omega

include hV in
theorem k542_of_clause [Finite X] (Ls : Subgroup (X ⧸ gnC T)) [IsSimpleGroup ↥Ls]
    (hnab : ∃ a b : ↥Ls, a * b ≠ b * a) {n : ℕ} (hn : 2 ≤ n)
    (hcard : (n = 4 ∧ Nat.card ↥Ls = 360) ∨ (n = 6 ∧ Nat.card ↥Ls = 6048))
    (hHI : HasIrreducibleCommutatorQuotient (Ls.comap (QuotientGroup.mk' (gnC T))) (gnV T))
    (hrel : (⁅gnV T, Ls.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
          Subgroup.centralizer (Ls.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
        ⁅gnV T, Ls.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ n)
    (x : X) (hx : QuotientGroup.mk' (gnC T) x ∈ Subgroup.centralizer (Ls : Set (X ⧸ gnC T))) :
    ∀ u ∈ ⁅gnV T, Ls.comap (QuotientGroup.mk' (gnC T))⁆,
      x * u * x⁻¹ * u⁻¹ ∈ ⁅gnV T, Ls.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
        Subgroup.centralizer ((Ls.comap (QuotientGroup.mk' (gnC T)) : Subgroup X) : Set X) := by
  classical
  intro u hu
  set ρ := gnRep hV with hρ
  set L' := Ls.comap (QuotientGroup.mk' (gnC T)) with hL'
  set U := commOn ρ Ls ⊤ with hU
  set C := fixOn ρ Ls U with hC
  set g := QuotientGroup.mk' (gnC T) x with hg
  have hUs : subOf hV U = ⁅gnV T, L'⁆ := subOf_commOn hV Ls
  have hCs : subOf hV C = ⁅gnV T, L'⁆ ⊓ Subgroup.centralizer (L' : Set X) := by
    rw [hC, subOf_fixOn, hUs]
  obtain ⟨hirr, hdim⟩ := clause_to_module hV Ls hHI hrel
  have hcomm : ∀ a ∈ Ls, a * g = g * a := fun a ha => Subgroup.mem_centralizer_iff.mp hx a ha
  have hnorm : ∀ g' : X ⧸ gnC T, (∀ a ∈ Ls, a * g' = g' * a) →
      g' ∈ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
    intro g' hg'
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have e1 : ∀ b ∈ Ls, g' * b * g'⁻¹ = b := fun b hb => by
      rw [← hg' b hb]; group
    have e2 : ∀ b ∈ Ls, g'⁻¹ * b * g' = b := fun b hb => by
      calc g'⁻¹ * b * g' = g'⁻¹ * (b * g') := by group
        _ = g'⁻¹ * (g' * b) := by rw [hg' b hb]
        _ = b := by group
    refine ⟨fun ha => by rw [e1 a ha]; exact ha, fun ha => ?_⟩
    have h3 : a = g' * a * g'⁻¹ :=
      calc a = g'⁻¹ * (g' * a * g'⁻¹) * g' := by group
        _ = g' * a * g'⁻¹ := e2 _ ha
    rw [h3]
    exact ha
  have hmapU : ∀ g' : X ⧸ gnC T, (∀ a ∈ Ls, a * g' = g' * a) → ∀ w ∈ U, ρ g' w ∈ U :=
    fun g' hg' w hw => commOn_top_mapsTo (hnorm g' hg') hw
  have hmapC : ∀ g' : X ⧸ gnC T, (∀ a ∈ Ls, a * g' = g' * a) → ∀ c ∈ C, ρ g' c ∈ C := by
    intro g' hg' c hc
    refine mem_fixOn.mpr ⟨hmapU g' hg' c (mem_fixOn.mp hc).1, fun a ha => ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, hg' a ha, map_mul, Module.End.mul_apply,
      (mem_fixOn.mp hc).2 a ha]
  have hmain : ∀ w ∈ U, ρ g w - w ∈ C := by
    refine endo_rel (π := ρ.comp Ls.subtype) (ξ := ρ g) hnab hn hcard U C
      (fun v hv => (mem_fixOn.mp hv).1) ?_ ?_ (hmapU g hcomm) (hmapC g hcomm) ?_ ?_ hdim ?_
    · exact fun h u hu => isInvariant_commOn_top (Subgroup.le_normalizer) h.1 h.2 u hu
    · intro h c hc
      show ρ h.1 c ∈ C
      rw [(mem_fixOn.mp hc).2 h.1 h.2]
      exact hc
    · intro h w
      show ρ h.1 (ρ g w) = ρ g (ρ h.1 w)
      rw [← Module.End.mul_apply, ← map_mul, hcomm h.1 h.2, map_mul, Module.End.mul_apply]
    · intro Z hZ hCZ hZU
      exact hirr Z (fun a ha z hz => hZ ⟨a, ha⟩ z hz) hCZ hZU
    · intro w hw hwC
      have hcg : ∀ a ∈ Ls, a * g⁻¹ = g⁻¹ * a := fun a ha =>
        Commute.inv_right (show Commute a g from hcomm a ha)
      have := hmapC g⁻¹ hcg _ hwC
      rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        at this
  obtain ⟨w, hwU, rfl⟩ := (mem_subOf hV).1 (show u ∈ subOf hV U by rw [hUs]; exact hu)
  rw [← hCs]
  refine ⟨ρ g w - w, hmain w hwU, ?_⟩
  rw [elt_sub]
  have e : elt hV (ρ g w) = x * elt hV w * x⁻¹ := elt_gnRep hV x w
  rw [e]

end Glue

section Final

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

theorem nonabelian_of_simple_card {Y : Type} [Group Y] [IsSimpleGroup Y] {m : ℕ}
    (hm : ¬ m.Prime) (hcard : Nat.card Y = m) : ∃ a b : Y, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  let _ : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hcon }
  have := IsSimpleGroup.prime_card (α := Y)
  rw [hcard] at this
  exact hm this

section Certified

theorem u33_simple_card {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq3 : q.card = 3) (hqd : d.1 = .twistedA 2 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : IsSimpleGroup Y ∧ Nat.card Y = 6048 := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hqd
  subst hqd
  have hm0 := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  obtain ⟨hp3, he1⟩ : q.p = 3 ∧ q.exponent = 1 :=
    (Nat.Prime.pow_eq_iff Nat.prime_three).mp (by rw [← TauCeti.PrimePower.card_def]; exact hq3)
  rw [hp3, he1] at hm0
  have hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSU 3 3 1 := hm0
  obtain ⟨eU⟩ := nonempty_mulEquiv_u33G_of_statedClassicalModel hm
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  exact ⟨eU.isSimpleGroup, CFSG.Quasithin.G11.Harris.G2.card_of_statedModel hm⟩

end Certified

end Final

end K542Proof

section Main

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

theorem K542_holds : K542 := by
  intro X _ _ T hX Ls hL hJ h6 x hx
  have hC : CharTwo (⊤ : Subgroup X) := hX.charTwo
  have hT2 : IsPGroup 2 T := hX.sylow.isPGroup
  have hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow
  have hV := isElemAbelian_gnV_of_le hC hQT
  letI : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  rcases h6 with h6 | ⟨d, q, hq3, hqd, he⟩
  · obtain ⟨eL⟩ := h6
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := isSimpleGroup_alt6
    haveI : IsSimpleGroup ↥Ls := eL.isSimpleGroup
    have hcard : Nat.card ↥Ls = 360 := by
      rw [Nat.card_congr eL.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    obtain ⟨hHI, hrel⟩ := a6_clause T hC hQT Ls hL hJ eL
    exact K542Proof.k542_of_clause hV Ls (K542Proof.nonabelian_of_simple_card (by norm_num) hcard)
      (n := 4) (by norm_num) (Or.inl ⟨rfl, hcard⟩) hHI hrel x hx
  · obtain ⟨e⟩ := he
    obtain ⟨hs, hcard⟩ := K542Proof.u33_simple_card hq3 hqd e
    haveI := hs
    obtain ⟨hHI, hrel⟩ := agl81FiveThreeU33_proved X T hX.kGroup hC hT2 hQT Ls hL hJ
      ⟨d, ⟨q, hq3, hqd⟩, ⟨e⟩⟩
    exact K542Proof.k542_of_clause hV Ls (K542Proof.nonabelian_of_simple_card (by norm_num) hcard)
      (n := 6) (by norm_num) (Or.inr ⟨rfl, hcard⟩) hHI hrel x hx

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15
