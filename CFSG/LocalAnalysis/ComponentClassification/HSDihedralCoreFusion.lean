module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Harada
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitInputs

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.HarrisLit
open CFSG.ComponentClassification.HSFLit (HaradaInput ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

namespace LocalDatum

variable (Δ : LocalDatum X A)

omit [Finite X] in
theorem gen4_S (hA : AutFacts Δ) (P : Subgroup X) (hP : P ≤ Δ.S) :
    ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  classical
  set H := P.subgroupOf Δ.S
  obtain ⟨s, hs, hsH⟩ := hA.gen3 (H.map Δ.ψ) (map_le_range _ _)
  have : IsCyclic ↥(H ⊓ Δ.ψ.ker) := by
    have := Δ.isCyclic_ker
    have h1 : IsCyclic ↥((H ⊓ Δ.ψ.ker).subgroupOf Δ.ψ.ker) := inferInstance
    exact (subgroupOfEquivOfLe inf_le_right).isCyclic.mp h1
  obtain ⟨r, hr, hrH⟩ := HSFLit.exists_finset_closure_eq_of_isCyclic (H ⊓ Δ.ψ.ker)
  obtain ⟨u, hu, huH⟩ := HSFLit.exists_finset_closure_eq_of_map Δ.ψ H hs hsH hr hrH
  refine ⟨u.image Δ.S.subtype, Finset.card_image_le.trans hu, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, huH, subgroupOf_map_subtype,
    inf_of_le_left hP]

theorem exists_sylow_ne (hA : AutFacts Δ) (hX : ¬ SectionalRankLeFour X) :
    ∃ T : Sylow 2 X, Δ.S ≤ T ∧ Δ.S ≠ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := Δ.sylow.isPGroup.exists_le_sylow
  refine ⟨T, hT, fun h => hX ?_⟩
  intro P hP
  refine HSFLit.exists_finset_closure_eq_of_sylow T (fun U hU => ?_) P hP
  exact Δ.gen4_S hA U (h ▸ hU)

theorem mem_S_of_commute_t {T : Subgroup X} (hT : IsPGroup 2 T) (hST : Δ.S ≤ T) {y : X}
    (hy : y ∈ T) (hyt : y * Δ.t = Δ.t * y) : y ∈ Δ.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Δ.S ⊔ zpowers y ≤ T ⊓ centralizer ({Δ.t} : Set X) := by
    refine sup_le (le_inf hST Δ.sylow.le) ?_
    rw [zpowers_le]
    exact ⟨hy, mem_centralizer_singleton_iff.mpr hyt⟩
  have h2 : IsPGroup 2 (Δ.S ⊔ zpowers y : Subgroup X) := hT.to_le (hle.trans inf_le_left)
  have heq := Δ.sylow.eq_of_le le_sup_left (hle.trans inf_le_right) h2
  rw [← heq]
  exact mem_sup_right (mem_zpowers y)

theorem mem_S_of_conj_t {T : Subgroup X} (hT : IsPGroup 2 T) (hST : Δ.S ≤ T) {x : X}
    (hx : x ∈ T) (hxt : x * Δ.t * x⁻¹ = Δ.t) : x ∈ Δ.S :=
  Δ.mem_S_of_commute_t hT hST hx (by
    calc x * Δ.t = x * Δ.t * x⁻¹ * x := by group
      _ = Δ.t * x := by rw [hxt])

theorem exists_fusion (hA : AutFacts Δ) (hX : ¬ SectionalRankLeFour X) :
    ∃ T : Sylow 2 X, Δ.S ≤ T ∧ ∃ x ∈ (T : Subgroup X), x ∉ Δ.S ∧
      ∀ s ∈ Δ.S, x * s * x⁻¹ ∈ Δ.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hST, hne⟩ := Δ.exists_sylow_ne hA hX
  refine ⟨T, hST, ?_⟩
  have hnil : Group.IsNilpotent ↥(T : Subgroup X) := T.isPGroup'.isNilpotent
  have hlt : Δ.S.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hST ?_)
    intro y hy
    have : (⟨y, hy⟩ : ↥(T : Subgroup X)) ∈ Δ.S.subgroupOf T := h ▸ mem_top _
    exact this
  have := Group.normalizerCondition_of_isNilpotent _ hlt
  obtain ⟨⟨x, hxT⟩, hxN, hxS⟩ := IsConcreteLE.exists_of_lt this
  refine ⟨x, hxT, fun h => hxS (mem_subgroupOf.mpr h), fun s hs => ?_⟩
  have h1 := (mem_normalizer_iff.mp hxN ⟨s, hST hs⟩).mp (mem_subgroupOf.mpr hs)
  exact mem_subgroupOf.mp h1

theorem false_of_harada (hH : HaradaInput) (hA : AutFacts Δ) (hX : ¬ SectionalRankLeFour X)
    {E : Subgroup X} (hES : E ≤ Δ.S) (htE : Δ.t ∈ E) (hE : ElemAbelianTwo E)
    (hcard : Nat.card E = 8) (hC : ∀ s ∈ Δ.S, (∀ e ∈ E, s * e = e * s) → s ∈ E) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hST, -⟩ := Δ.exists_sylow_ne hA hX
  apply hX
  refine HSFLit.gen4_of_harada hH T (hES.trans hST) hE hcard (fun y hy hyE => ?_)
  have hyt : y * Δ.t = Δ.t * y := hyE _ htE
  exact hC y (Δ.mem_S_of_commute_t T.isPGroup' hST hy hyt) hyE

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
