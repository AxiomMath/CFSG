module

public import CFSG.CGT.PushingUpLit.Glue.NaturalIrred
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteen
public import CFSG.CGT.PushingUpLit.BHS.BlockStatements

public section

namespace CFSG.CGT.PushingUpLit.Glue

open CFSG CFSG.RankThree.PartOne

section Abstract

variable {L : Type*} [Group L] {U C : Subgroup L} {V : Type*} [AddCommGroup V]

theorem irreducible_of_module (ψ : ↥U →* Multiplicative V) (hk : ψ.ker = C.subgroupOf U)
    (W : AddSubgroup V) (hW : ∀ u : U, Multiplicative.toAdd (ψ u) ∈ W)
    (hirr : ∀ X : AddSubgroup V, X ≤ W →
      (∀ (l : L) (u : U) (hu' : l * u * l⁻¹ ∈ U), Multiplicative.toAdd (ψ u) ∈ X →
        Multiplicative.toAdd (ψ ⟨l * u * l⁻¹, hu'⟩) ∈ X) → X = ⊥ ∨ X = W)
    (N : Subgroup L) [hN : N.Normal] (hNU : N ≤ U) (hCN : C ≤ N) : N = C ∨ N = U := by
  let X : AddSubgroup V :=
    { carrier := {v | ∃ u : U, (u : L) ∈ N ∧ Multiplicative.toAdd (ψ u) = v}
      zero_mem' := ⟨1, N.one_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', N.mul_mem hu hu', by simp [toAdd_mul]⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, N.inv_mem hu, by simp⟩ }
  have hXmem : ∀ u : U, Multiplicative.toAdd (ψ u) ∈ X ↔ (u : L) ∈ N := by
    intro u
    constructor
    · rintro ⟨u', hu', h⟩
      have h1 : ψ u' = ψ u := by
        have := congrArg Multiplicative.ofAdd h
        simpa using this
      have h2 : u'⁻¹ * u ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      rw [hk] at h2
      have h3 : ((u'⁻¹ * u : U) : L) ∈ C := h2
      have h4 : ((u'⁻¹ * u : U) : L) ∈ N := hCN h3
      have h5 : (u : L) = (u' : L) * ((u'⁻¹ * u : U) : L) := by simp
      rw [h5]
      exact N.mul_mem hu' h4
    · intro hu
      exact ⟨u, hu, rfl⟩
  have hXW : X ≤ W := by
    rintro _ ⟨u, -, rfl⟩
    exact hW u
  have hinv : ∀ (l : L) (u : U) (hu' : l * u * l⁻¹ ∈ U), Multiplicative.toAdd (ψ u) ∈ X →
      Multiplicative.toAdd (ψ ⟨l * u * l⁻¹, hu'⟩) ∈ X := by
    intro l u hu' hu
    rw [hXmem] at hu ⊢
    exact hN.conj_mem _ hu l
  rcases hirr X hXW hinv with hX | hX
  · left
    refine le_antisymm (fun n hn => ?_) hCN
    have hmem : Multiplicative.toAdd (ψ ⟨n, hNU hn⟩) ∈ X := (hXmem ⟨n, hNU hn⟩).mpr hn
    rw [hX, AddSubgroup.mem_bot] at hmem
    have h1 : ψ ⟨n, hNU hn⟩ = 1 := by
      have := congrArg Multiplicative.ofAdd hmem
      simpa using this
    have h2 : (⟨n, hNU hn⟩ : U) ∈ ψ.ker := h1
    rw [hk] at h2
    exact h2
  · right
    refine le_antisymm hNU (fun u hu => ?_)
    have hmem : Multiplicative.toAdd (ψ ⟨u, hu⟩) ∈ X := by
      rw [hX]
      exact hW ⟨u, hu⟩
    exact (hXmem ⟨u, hu⟩).mp hmem

end Abstract

section Natural

variable {L : Type} [Group L]

instance shortU_normal : (shortU L).Normal := by
  unfold shortU
  infer_instance

theorem irreducible_of_isNaturalSLTwoModule {n : ℕ} (h : IsNaturalSLTwoModule L n)
    (N : Subgroup L) [N.Normal] (hNU : N ≤ shortU L) (hCN : shortC L ≤ N) :
    N = shortC L ∨ N = shortU L := by
  obtain ⟨φ, ψ, hs, hk, he⟩ := h
  refine irreducible_of_module ψ hk ⊤ (fun _ => trivial) ?_ N hNU hCN
  intro X _ hinv
  refine sl2_invariant_eq_bot_or_top X fun g v hv => ?_
  obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd v)
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (φ.symm g)
  have hu' : l * (u : L) * l⁻¹ ∈ shortU L := shortU_normal.conj_mem _ u.2 l
  have h1 := hinv l u hu' (by rw [hu]; exact hv)
  have h2 := he l u u.2 hu'
  have hφ : φ (l : L ⧸ pCore 2 L) = g := by
    rw [hl]
    exact φ.apply_symm_apply g
  rw [h2] at h1
  simpa [hφ, hu] using h1

theorem irreducible_of_isNaturalAltModule {m : ℕ} (hm : 1 ≤ m) (h : IsNaturalAltModule L m)
    (N : Subgroup L) [N.Normal] (hNU : N ≤ shortU L) (hCN : shortC L ≤ N) :
    N = shortC L ∨ N = shortU L := by
  obtain ⟨φ, ψ, hsum, hs, hk, he⟩ := h
  refine irreducible_of_module ψ hk (evenWeight (2 * m + 1))
    (fun u => (mem_evenWeight_iff _).mpr (hsum u)) ?_ N hNU hCN
  intro X hXW hinv
  refine altInvariant_eq_bot_or_evenWeight ⟨m, rfl⟩ (by omega) X hXW fun σ hσ v hv => ?_
  obtain ⟨u, hu⟩ := hs v ((mem_evenWeight_iff _).mp (hXW hv))
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (φ.symm ⟨σ, hσ⟩)
  have hu' : l * (u : L) * l⁻¹ ∈ shortU L := shortU_normal.conj_mem _ u.2 l
  have hv' : Multiplicative.toAdd (ψ u) ∈ X := by
    rw [hu]
    exact hv
  have h1 : Multiplicative.toAdd (ψ ⟨l * (u : L) * l⁻¹, hu'⟩) ∈ X := hinv l u hu' hv'
  have h2 := he l u u.2 hu'
  have hφ : φ (l : L ⧸ pCore 2 L) = ⟨σ, hσ⟩ := by
    rw [hl]
    exact φ.apply_symm_apply _
  rw [h2] at h1
  simp only [toAdd_ofAdd, hφ] at h1
  have hu3 : Multiplicative.toAdd (ψ ⟨(u : L), u.2⟩) = v := by
    simpa using congrArg Multiplicative.toAdd hu
  rw [hu3] at h1
  exact h1

theorem isQuasisimple_sl2_galoisField {n : ℕ} (hn : 2 ≤ n) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : 4 ≤ (Finset.univ : Finset (GaloisField 2 n)).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hcard
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).2
      (CFSG.CGT.PushingUpLit.BHS.isQuasisimple_special_linear_two ⟨s, hs⟩))

theorem isQuasisimple_alternating {k : ℕ} (hk : 5 ≤ k) :
    CFSG.IsQuasisimple (alternatingGroup (Fin k)) :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).2
      (CFSG.CGT.PushingUpLit.BHS.isQuasisimple_alternatingGroup hk))

variable [Finite L]

theorem isShortGroup_of_natural (hchar : CFSG.IsCharacteristicP 2 L) (hres : oResidualTwo L = ⊤)
    (hab : ∀ x ∈ pCore 2 L, ∀ y ∈ pCore 2 L, x * y = y * x)
    (htype : (∃ n : ℕ, 2 ≤ n ∧ IsNaturalSLTwoModule L n) ∨
      ∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule L m) : IsShortGroup L where
  fitting_eq := (isCharacteristicP_iff_generalizedFitting_eq_pCore L 2).1 hchar
  residual_eq := hres
  quotient_type := by
    rcases htype with ⟨n, hn, φ, -⟩ | ⟨m, hm, φ, -⟩
    · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm (isQuasisimple_sl2_galoisField hn))
    · by_cases hm1 : m = 1
      · subst hm1
        right
        rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp only [Fintype.card_fin]
        norm_num [Nat.factorial]
      · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm
          (isQuasisimple_alternating (k := 2 * m + 1) (by omega)))
  U_le_center := by
    intro u hu
    have hu' : u ∈ ⁅pCore 2 L, (⊤ : Subgroup L)⁆ := hu
    have hP : u ∈ pCore 2 L := Subgroup.commutator_le_left _ _ hu'
    refine ⟨⟨u, hP⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (hab g g.2 u hP)
  nonzero := by
    refine lt_of_le_of_ne inf_le_left fun hCU => ?_
    have hUC : shortU L ≤ shortC L := le_of_eq hCU.symm
    rcases htype with ⟨n, hn, φ, ψ, hs, hk, -⟩ | ⟨m, hm, φ, ψ, hsum, hs, hk, -⟩
    · have hker : ψ.ker = ⊤ := by
        rw [hk]
        exact Subgroup.subgroupOf_eq_top.mpr hUC
      obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd (fun _ : Fin 2 => (1 : GaloisField 2 n)))
      have h1 : ψ u = 1 := by
        have := MonoidHom.ker_eq_top_iff.mp hker
        rw [this]
        rfl
      rw [h1] at hu
      have h2 := congrArg Multiplicative.toAdd hu
      have h3 := congrFun h2 0
      simp at h3
    · have hker : ψ.ker = ⊤ := by
        rw [hk]
        exact Subgroup.subgroupOf_eq_top.mpr hUC
      let a : Fin (2 * m + 1) := ⟨0, by omega⟩
      let b : Fin (2 * m + 1) := ⟨1, by omega⟩
      have hab' : a ≠ b := by
        intro h
        have := congrArg Fin.val h
        simp [a, b] at this
      obtain ⟨u, hu⟩ := hs (pairVec a b) ((mem_evenWeight_iff _).mp (pairVec_mem_evenWeight a b))
      have h1 : ψ u = 1 := by
        have := MonoidHom.ker_eq_top_iff.mp hker
        rw [this]
        rfl
      rw [h1] at hu
      have h2 := congrArg Multiplicative.toAdd hu
      have h3 := congrFun h2 a
      simp [pairVec, hab'] at h3
  irreducible := by
    intro N hN hNU hCN
    have := hN
    rcases htype with ⟨n, hn, h⟩ | ⟨m, hm, h⟩
    · exact irreducible_of_isNaturalSLTwoModule h N hNU hCN
    · exact irreducible_of_isNaturalAltModule hm h N hNU hCN

end Natural

section BTBlock

variable {Γ : Type} [Group Γ] {G T E : Subgroup Γ}

theorem pCore_abelian_of_isBTBlock (h : BHS.IsBTBlock G T E) :
    ∀ x ∈ pCore 2 ↥E, ∀ y ∈ pCore 2 ↥E, x * y = y * x := by
  intro x hx y hy
  have hx' : (x : Γ) ∈ CFSG.Open.pCoreOf 2 E := Subgroup.mem_map_of_mem E.subtype hx
  have hy' : (y : Γ) ∈ CFSG.Open.pCoreOf 2 E := Subgroup.mem_map_of_mem E.subtype hy
  exact Subtype.ext (h.elemAbelian.1 _ hx' _ hy')

variable [Finite Γ]

theorem isShortGroup_of_isBTBlock (h : BHS.IsBTBlock G T E) (hchar : CFSG.QuasithinUnique.CharTwo E) :
    IsShortGroup ↥E :=
  isShortGroup_of_natural
    (CFSG.QuasithinUnique.EscapingLocal.isCharacteristicP_of_charTwo hchar) h.residual
    (pCore_abelian_of_isBTBlock h) h.type

theorem inClassX_of_isBTBlock (h : BHS.IsBTBlock G T E) (hchar : CFSG.QuasithinUnique.CharTwo E) : InClassX ↥E :=
  ⟨isShortGroup_of_isBTBlock h hchar,
    h.type.symm.imp (fun ⟨m, hm, h'⟩ => ⟨m, hm, h'⟩) (fun ⟨n, hn, h'⟩ => ⟨n, by omega, h'⟩)⟩

end BTBlock

end CFSG.CGT.PushingUpLit.Glue
