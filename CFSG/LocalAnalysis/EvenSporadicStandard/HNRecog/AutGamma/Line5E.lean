module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.LineGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.TableAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCard

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

@[expose] def m11SegA : ↥CFSG.Blueprint.NativeSporadic.M11 :=
  ⟨List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def m11SegB : ↥CFSG.Blueprint.NativeSporadic.M11 :=
  ⟨List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

theorem m11_triple : ∃ β ξ η : ↥CFSG.Blueprint.NativeSporadic.M11,
    β ^ 2 = 1 ∧ β ≠ 1 ∧ ξ ^ 2 = 1 ∧ ξ ≠ 1 ∧ η ^ 2 = 1 ∧ η ≠ 1 ∧ ξ ≠ β ∧
    (β * ξ) ^ 5 = 1 ∧ β * ξ ≠ 1 ∧ ((β * η) ^ 2) ^ 2 = 1 ∧ (β * η) ^ 2 ≠ 1 ∧
    (ξ * η) ^ 2 = 1 ∧ ξ * η ≠ 1 ∧ (β * (ξ * η)) ^ 6 = 1 ∧ (β * (ξ * η)) ^ 2 ≠ 1 ∧
    (β * (ξ * η)) ^ 3 ≠ 1 ∧ ((β * (ξ * η)) ^ 3) ^ 2 = 1 := by
  refine ⟨m11SegB * m11SegA * m11SegB * m11SegA * m11SegB⁻¹ * m11SegA * m11SegB⁻¹,
    m11SegB * m11SegB * m11SegA * m11SegB * m11SegB * m11SegA * m11SegB * m11SegB * m11SegA,
    m11SegA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide +kernel

structure M11Emb (a : G) where
  ι : ↥CFSG.Blueprint.NativeSporadic.M11 →* G
  injective : Function.Injective ι
  centralizes : ∀ w, ι w ∈ Gx a
  two_A : ∀ w, w ^ 2 = 1 → w ≠ 1 → IsConj a (ι w)
  card_cent : ∀ ρ, orderOf ρ = 5 → Nat.card ↥(Gx a ⊓ Gx (ι ρ)) ≤ 100

theorem M11Emb.nonempty [Finite G] (hL : F5Local G a z) : Nonempty (M11Emb a) := by
  obtain ⟨z₀, b₀, u₀, hT, -⟩ := hL.fusion1.self.rep_z
  obtain ⟨M, ⟨e⟩⟩ := hT.m11_unique_class.1
  let e' : ↥M ≃* ↥CFSG.Blueprint.NativeSporadic.M11 := e
  let ι : ↥CFSG.Blueprint.NativeSporadic.M11 →* G :=
    ((Gx a).subtype.comp M.subtype).comp e'.symm.toMonoidHom
  have hinj : Function.Injective ι :=
    (Subtype.coe_injective.comp Subtype.coe_injective).comp e'.symm.injective
  refine ⟨⟨ι, hinj, fun w => (e'.symm w).1.2, ?_, ?_⟩⟩
  · intro w hw hw1
    let Mg : Subgroup G := M.map (Gx a).subtype
    have hMg : Mg ≤ Gx a := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hsp : IsSporadic ↥Mg .M11 :=
      ⟨(Subgroup.equivMapOfInjective M (Gx a).subtype Subtype.coe_injective).symm.trans e⟩
    refine hL.cube.self.m11_two_A Mg hMg hsp (ι w) ⟨(e'.symm w : ↥(Gx a)), (e'.symm w).2, rfl⟩
      ?_ ?_
    · rw [← map_pow, hw, map_one]
    · intro h
      exact hw1 (hinj (by rw [h, map_one]))
  · intro ρ hρ
    let ρ' : ↥(Gx a) := (e'.symm ρ : ↥M)
    have hord : orderOf ρ' = 5 := by
      rw [show ρ' = ((e'.symm ρ : ↥M) : ↥(Gx a)) from rfl, Subgroup.orderOf_coe,
        MulEquiv.orderOf_eq]
      exact hρ
    have h100 := (hT.m11_centralizer_five M ⟨e⟩ ρ' (e'.symm ρ).2 hord).card_eq
    refine le_of_le_of_eq (Nat.card_le_card_of_injective
      (fun g : ↥(Gx a ⊓ Gx (ι ρ)) => (⟨⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, ?_⟩ :
        ↥(Subgroup.centralizer ({ρ'} : Set ↥(Gx a))))) ?_) h100
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact (mem_Gx.1 (Subgroup.mem_inf.1 g.2).2 : ι ρ * g.1 = g.1 * ι ρ).symm
    · intro g g' h
      exact Subtype.ext (congrArg (fun x : ↥(Subgroup.centralizer ({ρ'} : Set ↥(Gx a))) =>
        ((x : ↥(Gx a)) : G)) h)

theorem hasLine_5E [Finite G] (hL : F5Local G a z) : HasLine a z .k5E .k4B .k6A := by
  obtain ⟨E⟩ := M11Emb.nonempty hL
  obtain ⟨β, ξ, η, hβ2, hβ1, hξ2, hξ1, hη2, hη1, hξβ, h5, h51, h4, h41, hxy2, hxy1, h6, h62, h63,
    h3sq⟩ := m11_triple
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hb : IsConj a (E.ι β) := E.two_A β hβ2 hβ1
  have ho5' : orderOf (β * ξ) = 5 := orderOf_eq_prime h5 h51
  have ho5 : orderOf (E.ι β * E.ι ξ) = 5 := by
    rw [← map_mul, orderOf_injective E.ι E.injective, ho5']
  have hcom : ∀ w, a ∈ Gx (E.ι w) := fun w => mem_Gx.2 (mem_Gx.1 (E.centralizes w)).symm
  have hy : E.ι ξ ∈ oddSet a (E.ι β) :=
    ⟨E.two_A ξ hξ2 hξ1, fun h => hξβ (E.injective h), by rw [ho5]; decide, a, IsConj.refl a,
      mem_Gxy.2 ⟨hcom β, hcom ξ⟩⟩
  have hlt : Nat.card ↥(Gxyz (E.ι β) a (E.ι ξ)) < 240 := by
    have hle : Gxyz (E.ι β) a (E.ι ξ) ≤ Gx a ⊓ Gx (E.ι (β * ξ)) := by
      intro g hg
      obtain ⟨h1, h2, h3⟩ := mem_Gxyz.1 hg
      refine Subgroup.mem_inf.2 ⟨h2, mem_Gx.2 ?_⟩
      rw [map_mul, mul_assoc, mem_Gx.1 h3, ← mul_assoc, mem_Gx.1 h1, mul_assoc]
    calc Nat.card ↥(Gxyz (E.ι β) a (E.ι ξ)) ≤ Nat.card ↥(Gx a ⊓ Gx (E.ι (β * ξ))) :=
          Subgroup.card_le_of_le hle
      _ ≤ 100 := E.card_cent (β * ξ) ho5'
      _ < 240 := by norm_num
  refine ⟨E.ι β, hb, E.ι ξ, mem_orb5E_of_card_lt hL hb hy ho5 (IsConj.refl a)
    (mem_Gxy.2 ⟨hcom β, hcom ξ⟩) hlt, E.ι η, ⟨E.two_A η hη2 hη1, ?_⟩, ?_⟩
  · rw [← map_mul, ← map_pow]
    exact E.two_A _ h4 h41
  · rw [← map_mul]
    refine ⟨E.two_A _ hxy2 hxy1, ?_, ?_⟩
    · rw [← map_mul, orderOf_injective E.ι E.injective]
      exact orderOf_eq_six h6 h62 h63
    · rw [← map_mul, ← map_pow]
      exact E.two_A _ h3sq h63

theorem line_5E [Finite G] (hL : F5Local G a z) :
    ∀ x ∈ orb5E a a, ∃ y ∈ orb4B a a, x * y ∈ orb6A a a :=
  line_of_hasLine (k₁ := .k5E) (k₂ := .k4B) (k₃ := .k6A) (isConjOrbit_orb5E hL) (hasLine_5E hL)

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
