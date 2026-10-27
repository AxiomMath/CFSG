module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Prop
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecHyp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bSection
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

namespace Hyp52

theorem nonempty_equiv_quot_T_of_eq {h h' : Hyp52 X} (hB : h'.B = h.B) (hT : h'.T = h.T)
    {A : Type*} [Mul A] (hA : Nonempty (A ≃* ↥h'.T ⧸ h'.B.subgroupOf h'.T)) :
    Nonempty (A ≃* ↥h.T ⧸ h.B.subgroupOf h.T) := by
  obtain ⟨e⟩ := hA
  refine ⟨e.trans (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hT) ?_)⟩
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hu
    rw [mem_subgroupOf, ← hB]
    exact hu
  · intro ht
    refine ⟨(MulEquiv.subgroupCongr hT).symm t, ?_, by simp⟩
    rw [mem_subgroupOf] at ht
    rw [SetLike.mem_coe, mem_subgroupOf, hB]
    exact ht

theorem sectionData_of_eq {h h' : Hyp52 X} (ha : h'.a = h.a) (hJ : h'.J = h.J)
    (hB : h'.B = h.B) (hK : h'.K = h.K) (hT : h'.T = h.T) (hd : h'.SectionData) :
    h.SectionData := by
  obtain ⟨H', i1, i2, k, eT, rest⟩ := hd
  refine ⟨H', i1, i2, k, nonempty_equiv_quot_T_of_eq hB hT eT, ?_⟩
  clear eT hT hB
  cases h'
  subst ha hJ hK
  exact rest

theorem exists_reChoice58 [IsSimpleGroup X] (hS : SchreierFor Blueprint.Catalog)
    (hnonab : ∃ u v : X, u * v ≠ v * u) (hK : Assembly.KProper Blueprint.Catalog X)
    (h : Hyp52 X) (hmax : GSMaximalUnbalancingTriple h.a h.x h.J)
    (hiso : GSIsoAt h.a h.J)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    {y : X} (hc : h.SecCond y) :
    ∃ h' : Hyp52 X, h'.a = h.a ∧ h'.J = h.J ∧ h'.B = h.B ∧ h'.K = h.K ∧
      (∃ c ∈ centralizer ({h.a} : Set X) ⊓ normalizer (h.J : Set X),
        h'.S = conjugate h.S c ∧ h'.x = c⁻¹ * h.x * c) ∧
      h'.Q = h.Q ∧ h'.T = h.T ∧ h'.SecCond y ∧
      Seven.IsSylowIn (h'.S ⊓ h'.secG0 y) (centralizer ({h'.a} : Set X) ⊓ h'.secG0 y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B₀ := h.B ⊓ conjugate h.B y with hB₀
  set E := zpowers h.a with hE
  have haE : h.a ∈ E := mem_zpowers _
  have hSC : h.S ≤ centralizer ({h.a} : Set X) := h.S_le.trans inf_le_left
  have hS2 : IsPGroup 2 h.S := by
    obtain ⟨R, hR⟩ := h.S_sylow
    have h1 : IsPGroup 2 (h.S.subgroupOf (centralizer ({h.a} : Set X) ⊓
        normalizer (h.J : Set X))) := hR ▸ R.isPGroup'
    have h2 := h1.map (centralizer ({h.a} : Set X) ⊓ normalizer (h.J : Set X)).subtype
    rwa [map_subgroupOf_eq_of_le h.S_le] at h2
  have hBS : h.B ≤ h.S := h.B_le.trans inf_le_left
  have hBC : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hyP : y ∈ h.P := hc.mem_P
  have hyS : y ∈ h.S := (mem_inf.mp hyP).1
  have hQB0 : h.Q ≤ normalizer (B₀ : Set X) := hc.Q_le
  have hyQ := hc.mem_normalizer_Q
  have hyB0 : y ∈ normalizer (B₀ : Set X) := mem_secG0_of_sq_mem hc.sq_mem_T
  have hBQ : h.B ≤ h.Q := le_inf hBS le_normalizer
  have hQS0 : h.Q ≤ h.S ⊓ normalizer (B₀ : Set X) := le_inf inf_le_left hQB0
  have hS0E : h.S ⊓ normalizer (B₀ : Set X) ≤ centralizer (E : Set X) := fun s hs => by
    rw [hE, centralizer_zpowers_eq]
    exact hSC (mem_inf.mp hs).1
  have hCSE := Six.sylow_centralizer_zpowers hSa
  set M := normalizer (B₀ : Set X) ⊓ centralizer (E : Set X) with hM
  have hS0M : h.S ⊓ normalizer (B₀ : Set X) ≤ M := le_inf inf_le_right hS0E
  have hS02 : IsPGroup 2 ((h.S ⊓ normalizer (B₀ : Set X)).subgroupOf M) :=
    (hS2.to_le inf_le_left).comap_subtype
  obtain ⟨RT, hRT⟩ := hS02.exists_le_sylow
  set T := (RT : Subgroup M).map M.subtype with hTdef
  have hTM : T ≤ M := map_subtype_le _
  have hS0T : h.S ⊓ normalizer (B₀ : Set X) ≤ T := fun z hz =>
    ⟨⟨z, hS0M hz⟩, hRT (mem_subgroupOf.mpr hz), rfl⟩
  have hT2 : IsPGroup 2 T := RT.isPGroup'.map _
  have hTE : T ≤ centralizer (E : Set X) := hTM.trans inf_le_right
  obtain ⟨g, hgE, hgT⟩ := exists_conjugate_le_of_sylow hCSE hTE hT2
  have hga : g ∈ centralizer ({h.a} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hgE h.a haE).symm
  have hca : g⁻¹ ∈ centralizer ({h.a} : Set X) := inv_mem hga
  have hgJ : g ∈ normalizer (h.J : Set X) := hCN hga
  have hcJ : g⁻¹ ∈ normalizer (h.J : Set X) := inv_mem hgJ
  set c := g⁻¹ with hcdef
  set S' := conjugate h.S c with hS'
  have hconjS' : conjugate S' g = h.S := by
    rw [hS', conjugate_conjugate, hcdef, inv_mul_cancel, conjugate_one]
  have hconjInf : ∀ A A' : Subgroup X, conjugate (A ⊓ A') g = conjugate A g ⊓ conjugate A' g :=
    fun A A' => Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective
  have hconjN : ∀ F : Subgroup X,
      conjugate (normalizer (F : Set X)) g = normalizer (conjugate F g : Set X) :=
    fun F => map_equiv_normalizer_eq F (MulAut.conj g⁻¹)
  have hconjC : conjugate (coreActionKernel h.J) g = coreActionKernel h.J :=
    Six.conjugate_coreActionKernel hgJ
  have hTS' : T ≤ S' := by
    intro t ht
    have h1 : g⁻¹ * t * g ∈ h.S := (mem_inf.mp (hgT (by
      rw [mem_conjugate_iff, show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
      exact ht))).1
    rw [hS', mem_conjugate_iff, hcdef, inv_inv]
    exact h1
  have hQT : h.Q ≤ T := hQS0.trans hS0T
  have hBT : h.B ≤ T := hBQ.trans hQT
  have hQS' : h.Q ≤ S' := hQT.trans hTS'
  have hyS0 : y ∈ h.S ⊓ normalizer (B₀ : Set X) := mem_inf.mpr ⟨hyS, hyB0⟩
  have hyS' : y ∈ S' := hTS' (hS0T hyS0)
  have hNQ : S' ⊓ normalizer (h.B : Set X) = h.Q := by
    have hcard : Nat.card ↥(S' ⊓ normalizer (h.B : Set X)) ≤ Nat.card h.Q := by
      by_contra hlt
      push Not at hlt
      set E' := conjugate h.B g with hE'
      have hE'S : E' ≤ h.S := (map_mono hBT).trans (hgT.trans inf_le_left)
      have hE'C : E' ≤ coreActionKernel h.J := by
        rw [← hconjC]
        exact map_mono hBC
      have hE'card : Nat.card E' = Nat.card h.B := GSLit.card_conjugate h.B g
      have hNE' : conjugate (S' ⊓ normalizer (h.B : Set X)) g =
          h.S ⊓ normalizer (E' : Set X) := by
        rw [hconjInf, hconjS', hconjN]
      have hlt' : Nat.card ↥(h.S ⊓ normalizer (h.B : Set X)) <
          Nat.card ↥(h.S ⊓ normalizer (E' : Set X)) := by
        rw [← hNE', GSLit.card_conjugate]
        exact hlt
      obtain ⟨L, hL⟩ := h.isoCorr_of_lt E' (le_inf hE'S hE'C) (Or.inr ⟨hE'card, hlt'⟩)
      have hL' := Six.isoCorrSub_conjugate hca hcJ hL
      rw [hE', conjugate_conjugate, mul_inv_cancel, conjugate_one] at hL'
      exact h.not_isoCorrSub_B _ hL'
    exact (eq_of_le_of_card_ge (le_inf hQS' inf_le_right) hcard).symm
  have hsyl' := Six.sylow_conjugate_of_mem h.S_le h.S_sylow (mem_inf.mpr ⟨hca, hcJ⟩)
  have hxx : h.x * h.x = 1 := by
    obtain ⟨-, hx, -⟩ := gsUnbalancingTriple_iff.mp hmax.1
    rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hmax' : GSMaximalUnbalancingTriple h.a (c⁻¹ * h.x * c) h.J :=
    ⟨gsUnbalancingTriple_conj hmax.1 hca hcJ, hmax.2⟩
  have hB2 : IsPGroup 2 h.B := hS2.to_le hBS
  have hBa : h.B ≤ centralizer ({h.a} : Set X) := hBS.trans hSC
  have hinfx : h.B ⊓ conjugate h.B (c⁻¹ * h.x * c) = ⊥ :=
    inf_conjugate_eq_bot hS hnonab hK hmax' hiso hB2 hBa hBC h.conjClosure_eq h.commutator_eq
  have hx'S : c⁻¹ * h.x * c ∈ S' := by
    rw [hS', mem_conjugate_iff, show c * (c⁻¹ * h.x * c) * c⁻¹ = h.x by group]
    exact h.x_mem
  have hx'sq : (c⁻¹ * h.x * c) ^ 2 = 1 := by
    rw [pow_two, show c⁻¹ * h.x * c * (c⁻¹ * h.x * c) = c⁻¹ * (h.x * h.x) * c by group, hxx]
    group
  have hcardQ : Nat.card ↥(S' ⊓ normalizer (h.B : Set X)) =
      Nat.card ↥(h.S ⊓ normalizer (h.B : Set X)) := by rw [hNQ]
  let h' : Hyp52 X :=
    { h with
      S := S'
      x := c⁻¹ * h.x * c
      S_le := hsyl'.1
      S_sylow := hsyl'.2
      B_le := le_inf (hBT.trans hTS') hBC
      isoCorr_of_lt := by
        intro F hF hFcard
        set F' := conjugate F g with hF'
        have hF'S : F' ≤ h.S ⊓ coreActionKernel h.J := by
          rw [← hconjS', ← hconjC, ← hconjInf]
          exact map_mono hF
        have hF'card : Nat.card F' = Nat.card F := GSLit.card_conjugate F g
        have hNF' : Nat.card ↥(h.S ⊓ normalizer (F' : Set X)) =
            Nat.card ↥(S' ⊓ normalizer (F : Set X)) := by
          rw [← GSLit.card_conjugate (S' ⊓ normalizer (F : Set X)) g, hconjInf, hconjS', hconjN]
        obtain ⟨L, hL⟩ := h.isoCorr_of_lt F' hF'S (by
          rw [hF'card, hNF', ← hcardQ]
          exact hFcard)
        refine ⟨conjugate L c, ?_⟩
        have := Six.isoCorrSub_conjugate hca hcJ hL
        rwa [hF', conjugate_conjugate, hcdef, mul_inv_cancel, conjugate_one] at this
      x_mem := hx'S
      inf_conjugate_x := hinfx
      x_sq_mem := by
        rw [hx'sq]
        exact one_mem _
      sylow_layer := by
        obtain ⟨R, hR1, hR2⟩ := h.sylow_layer
        exact ⟨R, hR1.trans (le_of_eq hNQ.symm), hR2⟩ }
  have hQ' : h'.Q = h.Q := hNQ
  have hT' : h'.T = h.T := by
    show h'.Q ⊓ (S' ⊓ coreActionKernel h.J) = h.Q ⊓ (h.S ⊓ coreActionKernel h.J)
    rw [hQ']
    apply le_antisymm
    · intro t ht
      obtain ⟨htQ, htP⟩ := mem_inf.mp ht
      exact mem_inf.mpr ⟨htQ, mem_inf.mpr ⟨(mem_inf.mp htQ).1, (mem_inf.mp htP).2⟩⟩
    · intro t ht
      obtain ⟨htQ, htP⟩ := mem_inf.mp ht
      exact mem_inf.mpr ⟨htQ, mem_inf.mpr ⟨hQS' htQ, (mem_inf.mp htP).2⟩⟩
  have hc' : h'.SecCond y := by
    refine ⟨mem_inf.mpr ⟨hyS', (mem_inf.mp hyP).2⟩, ?_, ?_, ?_, ?_⟩
    · rw [hT']
      exact hc.not_mem_T
    · rw [hT']
      exact hc.sq_mem_T
    · show h'.Q ≤ h.secG0 y
      rw [hQ']
      exact hc.Q_le
    · show y ∈ normalizer (h'.Q : Set X)
      rw [hQ']
      exact hyQ
  have hS'0E : S' ⊓ normalizer (B₀ : Set X) ≤ centralizer (E : Set X) := by
    intro s hs
    have hsa : s ∈ centralizer ({h.a} : Set X) := (mem_inf.mp (hsyl'.1 (mem_inf.mp hs).1)).1
    rw [hE, centralizer_zpowers_eq]
    exact hsa
  have hS'2 : IsPGroup 2 S' := hS2.map (MulAut.conj c⁻¹).toMonoidHom
  have hTeq : T = S' ⊓ normalizer (B₀ : Set X) := by
    have hle : T ≤ S' ⊓ normalizer (B₀ : Set X) := le_inf hTS' (hTM.trans inf_le_left)
    refine eq_of_le_of_card_ge hle ?_
    have hS'M : S' ⊓ normalizer (B₀ : Set X) ≤ M := le_inf inf_le_right hS'0E
    have h2 : IsPGroup 2 ((S' ⊓ normalizer (B₀ : Set X)).subgroupOf M) :=
      (hS'2.to_le inf_le_left).comap_subtype
    obtain ⟨R', hR'⟩ := h2.exists_le_sylow
    calc Nat.card ↥(S' ⊓ normalizer (B₀ : Set X))
        = Nat.card ((S' ⊓ normalizer (B₀ : Set X)).subgroupOf M) := by
          rw [Six.card_subgroupOf_eq, inf_eq_left.mpr hS'M]
      _ ≤ Nat.card R' := card_le_of_le hR'
      _ = Nat.card RT := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
      _ = Nat.card T := (card_map_of_injective M.subtype_injective).symm
  have hMeq : centralizer ({h.a} : Set X) ⊓ h.secG0 y = M := by
    rw [hM, hE, centralizer_zpowers_eq, inf_comm]
    rfl
  have hsylB : Seven.IsSylowIn (S' ⊓ h.secG0 y) (centralizer ({h.a} : Set X) ⊓ h.secG0 y) := by
    have hsec : h.secG0 y = normalizer (B₀ : Set X) := rfl
    rw [hMeq]
    refine ⟨le_inf inf_le_right (hsec ▸ hS'0E), RT, ?_⟩
    rw [hsec, ← hTeq, hTdef]
    exact (comap_map_eq_self_of_injective M.subtype_injective _).symm
  exact ⟨h', rfl, rfl, rfl, rfl, ⟨c, mem_inf.mpr ⟨hca, hcJ⟩, rfl, rfl⟩, hQ', hT', hc', hsylB⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
