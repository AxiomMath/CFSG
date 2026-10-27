module

public import CFSG.LieType.Steinberg.Minuscule.Datum
public import CFSG.LieType.Steinberg.PartBProof
public import CFSG.LieType.Steinberg.Presentation
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Universal
open scoped commutatorElement

variable {τ : Tag}

theorem mem_expPairs_iff (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (Φ : Steinberg.RootSystem (Fin τ.rank)) (hΦ : Φ.roots = {γ | IsRoot τ γ})
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α + β ≠ 0)
    (p : ℕ × ℕ) : p ∈ expPairs Φ α β ↔ IsRoot τ (α + β) ∧ p = (1, 1) := by
  simp only [expPairs, Set.mem_ofPred_eq, hΦ]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨e1, e2⟩ := eq_one_of_isRoot_nsmul_add_nsmul hpd hα hβ hne h1 h2 h3
    refine ⟨?_, Prod.ext e1 e2⟩
    rwa [e1, e2, one_smul, one_smul] at h3
  · rintro ⟨hr, rfl⟩
    exact ⟨one_pos, one_pos, by rwa [one_smul, one_smul]⟩

theorem list_eq_singleton_of_isRoot (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {Φ : Steinberg.RootSystem (Fin τ.rank)} (hΦ : Φ.roots = {γ | IsRoot τ γ}) (O : CommOrder Φ)
    {α β : Fin τ.rank → ℤ} (hα : α ∈ Φ.roots) (hβ : β ∈ Φ.roots) (hne : α + β ≠ 0)
    (hr : IsRoot τ (α + β)) : O.list α β = [(1, 1)] := by
  have hα' : IsRoot τ α := by rw [hΦ] at hα; exact hα
  have hβ' : IsRoot τ β := by rw [hΦ] at hβ; exact hβ
  refine MinData.Valid.eq_singleton_of_nodup (O.nodup α β) fun p => ?_
  rw [O.mem_iff α hα β hβ hne, mem_expPairs_iff hpd Φ hΦ hα' hβ' hne]
  exact and_iff_right hr

theorem list_eq_nil_of_not_isRoot (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {Φ : Steinberg.RootSystem (Fin τ.rank)} (hΦ : Φ.roots = {γ | IsRoot τ γ}) (O : CommOrder Φ)
    {α β : Fin τ.rank → ℤ} (hα : α ∈ Φ.roots) (hβ : β ∈ Φ.roots) (hne : α + β ≠ 0)
    (hr : ¬ IsRoot τ (α + β)) : O.list α β = [] := by
  have hα' : IsRoot τ α := by rw [hΦ] at hα; exact hα
  have hβ' : IsRoot τ β := by rw [hΦ] at hβ; exact hβ
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  rw [O.mem_iff α hα β hβ hne, mem_expPairs_iff hpd Φ hΦ hα' hβ' hne] at hp
  exact hr hp.1

open _root_.Classical in
@[expose] def commOrder (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (Φ : Steinberg.RootSystem (Fin τ.rank)) (hΦ : Φ.roots = {γ | IsRoot τ γ}) : CommOrder Φ where
  list α β := if IsRoot τ (α + β) then [(1, 1)] else []
  nodup α β := by split_ifs <;> simp
  mem_iff α hα β hβ hne p := by
    rw [hΦ] at hα hβ
    rw [mem_expPairs_iff hpd Φ hΦ hα hβ hne]
    split_ifs with hr <;> simp [hr]

theorem nonempty_commOrder (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (Φ : Steinberg.RootSystem (Fin τ.rank)) (hΦ : Φ.roots = {γ | IsRoot τ γ}) :
    Nonempty (CommOrder Φ) :=
  ⟨commOrder hpd Φ hΦ⟩

namespace MinData

namespace Valid

variable {D : MinData τ} (hV : D.Valid) (hA : TauCeti.IsFiniteType τ.cartan) (k : Type*)
  [Field k]

@[expose] def commC (α β : Fin τ.rank → ℤ) (_ : ℕ × ℕ) : ℤ := hV.commSign k α β

theorem commC_natAbs (α β : Fin τ.rank → ℤ) (p : ℕ × ℕ) : (hV.commC k α β p).natAbs = 1 := by
  rcases hV.commSign_eq_one_or k α β with h | h <;> simp [commC, h]

theorem commutatorFormula_commC (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (Φ : Steinberg.RootSystem (Fin τ.rank)) (hΦ : Φ.roots = {γ | IsRoot τ γ})
    (O : CommOrder Φ) : CommutatorFormula (hV.xm k) O (hV.commC k) := by
  intro α hα β hβ hne c d
  have hα' : IsRoot τ α := by rw [hΦ] at hα; exact hα
  have hβ' : IsRoot τ β := by rw [hΦ] at hβ; exact hβ
  by_cases hr : IsRoot τ (α + β)
  · rw [list_eq_singleton_of_isRoot hpd hΦ O hα hβ hne hr, List.map_singleton, List.prod_singleton,
      one_smul, one_smul, pow_one, pow_one, hV.commutator_xm_commSign k hα' hβ' hne hr]
    rfl
  · rw [list_eq_nil_of_not_isRoot hpd hΦ O hα hβ hne hr, List.map_nil, List.prod_nil,
      ((hV.commutator_xm k hα' hβ' hne).2 hr) c d]

theorem isUnit_of_commutatorFormula (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {Φ : Steinberg.RootSystem (Fin τ.rank)} (hΦ : Φ.roots = {γ | IsRoot τ γ}) {O : CommOrder Φ}
    {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula (hV.xm k) O C) {α β : Fin τ.rank → ℤ} (hα : α ∈ Φ.roots)
    (hβ : β ∈ Φ.roots) (hne : α + β ≠ 0) (hr : IsRoot τ (α + β)) :
    IsUnit (C α β (1, 1) : k) := by
  have hα' : IsRoot τ α := by rw [hΦ] at hα; exact hα
  have hβ' : IsRoot τ β := by rw [hΦ] at hβ; exact hβ
  obtain ⟨σ, hσ, hcomm⟩ := (hV.commutator_xm k hα' hβ' hne).1 hr
  have h := hC α hα β hβ hne 1 1
  rw [list_eq_singleton_of_isRoot hpd hΦ O hα hβ hne hr, List.map_singleton, List.prod_singleton,
    one_smul, one_smul, hcomm] at h
  have h' := hV.xm_injective k hr h
  simp only [mul_one, one_pow] at h'
  rw [← h']
  rcases hσ with rfl | rfl
  · exact isUnit_one
  · exact isUnit_one.neg

theorem weylElement_xm (i : Fin τ.rank) (t : kˣ) : weylElement (hV.xm k) i t = hV.nt k i t := by
  simp only [weylElement, nt]

theorem weylElement_conj {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (i : Fin τ.rank) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (t : kˣ) (u : k),
      weylElement (hV.xm k) i t * hV.xm k β u * (weylElement (hV.xm k) i t)⁻¹ =
        hV.xm k (reflection τ.cartan i β)
          ((ε : k) * ((t ^ (-(∑ j, τ.cartan i j * β j)) : kˣ) : k) * u) := by
  obtain ⟨σ, hσ, h⟩ := hV.nm_conj_xm k hβ i
  have key : ∀ (t : kˣ) (u : k),
      weylElement (hV.xm k) i t * hV.xm k β u * (weylElement (hV.xm k) i t)⁻¹ =
        hV.xm k (reflect τ i β) (((t ^ (-(∑ j, τ.cartan i j * β j)) : kˣ) : k) * (σ * u)) := by
    intro t u
    rw [weylElement_xm, nt_eq_hm_mul, mul_inv_rev,
      show hV.hm k i t * hV.nm k i * hV.xm k β u * ((hV.nm k i)⁻¹ * (hV.hm k i t)⁻¹) =
        hV.hm k i t * (hV.nm k i * hV.xm k β u * (hV.nm k i)⁻¹) * (hV.hm k i t)⁻¹ by group,
      h u, hV.hm_conj_xm k (hβ.reflect i), toWeight_reflect, reflectWeight_apply_self,
      toWeight_apply]
  have hrefl : reflection τ.cartan i β = reflect τ i β := by
    rw [reflection_apply]
    rfl
  rcases hσ with rfl | rfl
  · exact ⟨1, Or.inl rfl, fun t u => by rw [key, hrefl, Int.cast_one, one_mul, one_mul]⟩
  · exact ⟨-1, Or.inr rfl, fun t u => by
      rw [key, hrefl, Int.cast_neg, Int.cast_one]
      congr 1
      ring⟩

theorem slHom_mem (i : Fin τ.rank) (M : Matrix.SpecialLinearGroup (Fin 2) k) :
    hV.slHom k i M ∈ hV.minGroup k := by
  by_cases h0 : (M : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · obtain ⟨t, c, hc⟩ := sl_eq_of_lower_eq_zero k M h0
    have e : hV.slHom k i M =
        ((hV.hm k i t * hV.xm k (Pi.single i 1) c : hV.minGroup k) :
          (Module.End k (Fin D.d →₀ k))ˣ) := by
      ext1
      rw [slHom_val, hc, hV.blockOp_mul, hV.blockOp_diag, hV.blockOp_upper]
      show _ = hV.endo k (hV.hm k i t * hV.xm k (Pi.single i 1) c)
      rw [endo_mul, endo_hm, endo_xm]
    rw [e]
    exact Subtype.mem _
  · obtain ⟨u, t, v, hc⟩ := sl_eq_of_lower_ne_zero k M h0
    have e : hV.slHom k i M =
        ((hV.xm k (Pi.single i 1) u * hV.nm k i * hV.hm k i t * hV.xm k (Pi.single i 1) v :
          hV.minGroup k) : (Module.End k (Fin D.d →₀ k))ˣ) := by
      ext1
      rw [slHom_val, hc, hV.blockOp_mul, hV.blockOp_mul, hV.blockOp_mul, hV.blockOp_diag,
        hV.blockOp_upper, hV.blockOp_upper, hV.blockOp_weyl]
      show _ = hV.endo k
        (hV.xm k (Pi.single i 1) u * hV.nm k i * hV.hm k i t * hV.xm k (Pi.single i 1) v)
      rw [endo_mul, endo_mul, endo_mul, endo_xm, endo_nm, endo_hm, endo_xm]
    rw [e]
    exact Subtype.mem _

theorem exists_sl2Hom (i : Fin τ.rank) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* hV.minGroup k, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = hV.xm k (Pi.single i 1) c) ∧
        ∀ c, φ (sl2Lower c) = hV.xm k (-Pi.single i 1) c := by
  refine ⟨(hV.slHom k i).codRestrict _ (hV.slHom_mem k i), fun M N h => ?_, fun c => ?_,
    fun c => ?_⟩
  · have h' := congrArg (fun g : hV.minGroup k =>
      ((g : (Module.End k (Fin D.d →₀ k))ˣ) : Module.End k (Fin D.d →₀ k))) h
    exact Subtype.ext (hV.blockOp_injective k i h')
  · exact Subtype.ext (Units.ext (hV.blockOp_upper k i c))
  · exact Subtype.ext (Units.ext (hV.blockOp_lower k i c))

theorem rankTwo (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {Φ : Steinberg.RootSystem (Fin τ.rank)} (hΦ : Φ.roots = {γ | IsRoot τ γ}) {O : CommOrder Φ}
    {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula (hV.xm k) O C) (i : Fin τ.rank) {l : Fin τ.rank}
    (hl : τ.cartan l i = -1) :
    ∃ δ ∈ Φ.roots, ∃ γ ∈ Φ.roots, δ + γ ≠ 0 ∧ ∃ j : ℕ, (j = 1 ∨ j = 2) ∧
      Pi.single i 1 = δ + j • γ ∧ IsUnit (C δ γ (1, j) : k) := by
  have hsum : reflect τ l (Pi.single i 1) + -Pi.single l 1 = Pi.single i 1 := by
    rw [reflect_eq, toWeight_single, hl, neg_one_smul, sub_neg_eq_add, add_neg_cancel_right]
  have hδ : reflect τ l (Pi.single i 1) ∈ Φ.roots := by
    rw [hΦ]
    exact (IsRoot.basis i).reflect l
  have hγ : -Pi.single l 1 ∈ Φ.roots := by
    rw [hΦ]
    exact isRoot_neg_single τ l
  have hne : reflect τ l (Pi.single i 1) + -Pi.single l 1 ≠ 0 := by
    rw [hsum]
    exact (IsRoot.basis i).ne_zero
  refine ⟨_, hδ, _, hγ, hne, 1, Or.inl rfl, by rw [one_smul, hsum], ?_⟩
  exact hV.isUnit_of_commutatorFormula k hpd hΦ hC hδ hγ hne (by rw [hsum]; exact .basis i)

theorem minDatum_chevalleyExtras (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (hnb : ∀ i, ∃ l, τ.cartan l i = -1)
    (O : CommOrder (RootSystem.ofCartan (hV.minDatum hA k).isFiniteType
      (hV.minDatum hA k).divisible))
    (C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ)
    (hC : CommutatorFormula (hV.xm k) O C) :
    ChevalleyExtras (hV.minDatum hA k) k (hV.xm k) C O where
  param := hV.minDatum_isParametrization hA k _ (roots_eq hA)
  comm := hC
  weyl i β hβ := hV.weylElement_conj k ((hV.mem_minDatum_roots hA k).1 hβ) i
  rankOne i := hV.exists_sl2Hom k i
  prodInjective f L hnd hL hsort := hV.prodInjective_additive hpd f L hnd
    (fun γ hγ => ⟨(hV.mem_minDatum_roots hA k).1 (hL γ hγ).1, (hL γ hγ).2⟩) hsort
  rankTwo i := by
    obtain ⟨l, hl⟩ := hnb i
    exact hV.rankTwo k hpd (roots_eq hA) hC i hl

theorem minDatum_chevalleyExtras_commC (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (hnb : ∀ i, ∃ l, τ.cartan l i = -1)
    (O : CommOrder (RootSystem.ofCartan (hV.minDatum hA k).isFiniteType
      (hV.minDatum hA k).divisible)) :
    (∀ α ∈ (RootSystem.ofCartan (hV.minDatum hA k).isFiniteType (hV.minDatum hA k).divisible).roots,
      ∀ β ∈ (RootSystem.ofCartan (hV.minDatum hA k).isFiniteType
        (hV.minDatum hA k).divisible).roots,
      ∀ p ∈ expPairs (RootSystem.ofCartan (hV.minDatum hA k).isFiniteType
        (hV.minDatum hA k).divisible) α β, (hV.commC k α β p).natAbs ∈ ({1, 2, 3} : Set ℕ)) ∧
      ChevalleyExtras (hV.minDatum hA k) k (hV.xm k) (hV.commC k) O :=
  ⟨fun α _ β _ p _ => by rw [hV.commC_natAbs]; simp,
    hV.minDatum_chevalleyExtras hA k hpd hnb O _
      (hV.commutatorFormula_commC k hpd _ (roots_eq hA) O)⟩

theorem minDatum_presentationB [Finite k] (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (hnb : ∀ i, ∃ l, τ.cartan l i = -1)
    (hbij : Function.Bijective (stPi (RootSystem.ofCartan (hV.minDatum hA k).isFiniteType
      (hV.minDatum hA k).divisible) (hV.minDatum hA k).rootGroup)) :
    PresentationB (Φ := RootSystem.ofCartan (hV.minDatum hA k).isFiniteType
      (hV.minDatum hA k).divisible) (hV.xm k) := by
  intro O
  obtain ⟨hbound, -⟩ := hV.minDatum_chevalleyExtras_commC hA k hpd hnb O
  exact ⟨⟨hV.commC k, hbound, hV.commutatorFormula_commC k hpd _ (roots_eq hA) O⟩,
    fun C hC => chevPresented_bijective rfl (hV.minDatum_chevalleyExtras hA k hpd hnb O C hC)
      hbij⟩

theorem minDatum_redundantR2 [Finite k] (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (hnb : ∀ i, ∃ l, τ.cartan l i = -1)
    (hbij : Function.Bijective (stPi (RootSystem.ofCartan (hV.minDatum hA k).isFiniteType
      (hV.minDatum hA k).divisible) (hV.minDatum hA k).rootGroup)) :
    RedundantR2 (RootSystem.ofCartan (hV.minDatum hA k).isFiniteType
      (hV.minDatum hA k).divisible) (hV.minDatum hA k).rootGroup :=
  redundantR2 rfl
    (hV.minDatum_chevalleyExtras_commC hA k hpd hnb (commOrder hpd _ (roots_eq hA))).2 hbij

end Valid

end MinData

theorem neighbour_E6 : ∀ i : Fin (Tag.rank .E6), ∃ l, Tag.cartan .E6 l i = -1 := by decide

theorem neighbour_E7 : ∀ i : Fin (Tag.rank .E7), ∃ l, Tag.cartan .E7 l i = -1 := by decide

variable (k : Type*) [Field k]

theorem e6_nonempty_commOrder :
    Nonempty (CommOrder (RootSystem.ofCartan (e6Datum k).isFiniteType (e6Datum k).divisible)) :=
  nonempty_commOrder posDef_cartan_E6 _ (roots_eq isFiniteType_cartan_E6)

theorem e7_nonempty_commOrder :
    Nonempty (CommOrder (RootSystem.ofCartan (e7Datum k).isFiniteType (e7Datum k).divisible)) :=
  nonempty_commOrder posDef_cartan_E7 _ (roots_eq isFiniteType_cartan_E7)

theorem e6_chevalleyExtras
    (O : CommOrder (RootSystem.ofCartan (e6Datum k).isFiniteType (e6Datum k).divisible))
    (C : (Fin (Tag.rank .E6) → ℤ) → (Fin (Tag.rank .E6) → ℤ) → ℕ × ℕ → ℤ)
    (hC : CommutatorFormula (e6Data_valid.xm k) O C) :
    ChevalleyExtras (e6Datum k) k (e6Data_valid.xm k) C O :=
  e6Data_valid.minDatum_chevalleyExtras isFiniteType_cartan_E6 k posDef_cartan_E6 neighbour_E6 O
    C hC

theorem e7_chevalleyExtras
    (O : CommOrder (RootSystem.ofCartan (e7Datum k).isFiniteType (e7Datum k).divisible))
    (C : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ) → ℕ × ℕ → ℤ)
    (hC : CommutatorFormula (e7Data_valid.xm k) O C) :
    ChevalleyExtras (e7Datum k) k (e7Data_valid.xm k) C O :=
  e7Data_valid.minDatum_chevalleyExtras isFiniteType_cartan_E7 k posDef_cartan_E7 neighbour_E7 O
    C hC

theorem e6_presentationB [Finite k] :
    PresentationB (Φ := RootSystem.ofCartan (e6Datum k).isFiniteType (e6Datum k).divisible)
      (e6Data_valid.xm k) :=
  e6Data_valid.minDatum_presentationB isFiniteType_cartan_E6 k posDef_cartan_E6 neighbour_E6
    (bijective_stPi_of (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k)).2

theorem e7_presentationB [Finite k] :
    PresentationB (Φ := RootSystem.ofCartan (e7Datum k).isFiniteType (e7Datum k).divisible)
      (e7Data_valid.xm k) :=
  e7Data_valid.minDatum_presentationB isFiniteType_cartan_E7 k posDef_cartan_E7 neighbour_E7
    (bijective_stPi_of (e7Datum_isCTGroupDatum k) (e7Datum_steinbergExtras k)).2

theorem e6_redundantR2 [Finite k] :
    RedundantR2 (RootSystem.ofCartan (e6Datum k).isFiniteType (e6Datum k).divisible)
      (e6Datum k).rootGroup :=
  e6Data_valid.minDatum_redundantR2 isFiniteType_cartan_E6 k posDef_cartan_E6 neighbour_E6
    (bijective_stPi_of (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k)).2

theorem e7_redundantR2 [Finite k] :
    RedundantR2 (RootSystem.ofCartan (e7Datum k).isFiniteType (e7Datum k).divisible)
      (e7Datum k).rootGroup :=
  e7Data_valid.minDatum_redundantR2 isFiniteType_cartan_E7 k posDef_cartan_E7 neighbour_E7
    (bijective_stPi_of (e7Datum_isCTGroupDatum k) (e7Datum_steinbergExtras k)).2

end CFSG.LieType.Steinberg.Minuscule
