module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalCentral
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLang
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToral
public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Bridge

variable {τ : Tag} {K : Type} [Field K]

theorem subgroupOf_rootSubgroup_sup_eq (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    (rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ)).subgroupOf (adjointGroup τ K) =
      rootGroup F K γ ⊔ rootGroup F K (-γ) := by
  have h1 : (rootSubgroup τ K γ).subgroupOf (adjointGroup τ K) = rootGroup F K γ := by
    rw [rootGroup_of_isRoot hγ]
    exact F.subgroupOf_rootSubgroup_eq K ⟨γ, hγ⟩
  have hγ' : IsRoot τ (-γ) := IsRoot.neg hγ
  have h2 : (rootSubgroup τ K (-γ)).subgroupOf (adjointGroup τ K) = rootGroup F K (-γ) := by
    rw [rootGroup_of_isRoot hγ']
    exact F.subgroupOf_rootSubgroup_eq K ⟨-γ, hγ'⟩
  have hle1 : rootSubgroup τ K γ ≤ adjointGroup τ K := rootSubgroup_le_adjointGroup γ
  have hle2 : rootSubgroup τ K (-γ) ≤ adjointGroup τ K := rootSubgroup_le_adjointGroup (-γ)
  rw [← h1, ← h2]
  refine Subgroup.map_injective (adjointGroup τ K).subtype_injective ?_
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hle1, inf_eq_left.2 hle2,
    inf_eq_left.2 (sup_le hle1 hle2)]

theorem eq_rootGroup_sup_of_map_eq (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {L : Subgroup ↥(adjointGroup τ K)}
    (h : L.map (adjointGroup τ K).subtype = rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ)) :
    L = rootGroup F K γ ⊔ rootGroup F K (-γ) := by
  rw [← subgroupOf_rootSubgroup_sup_eq F hγ, ← h]
  exact (Subgroup.comap_map_eq_self_of_injective (adjointGroup τ K).subtype_injective L).symm

end Bridge

section Core

variable {τ : Tag} {p f : ℕ} [Fact p.Prime]

theorem exists_conj_eq_rootGroup_sup_of_isClassicalMember
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {L : Subgroup ↥(adjointGroup τ (GaloisField p f))} {z : ↥(adjointGroup τ (GaloisField p f))}
    (h : IsClassicalMember p f L z) :
    ∃ (g : ↥(adjointGroup τ (GaloisField p f))) (b : Fin τ.rank → (GaloisField p f)ˣ)
      (γ : Fin τ.rank → ℤ) (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      L = (rootGroup (rootOperatorFamily τ) (GaloisField p f) γ ⊔
          rootGroup (rootOperatorFamily τ) (GaloisField p f) (-γ)).map
          (MulAut.conj g⁻¹).toMonoidHom ∧
        componentRootSpan (GaloisField p f) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
          rootSubgroup τ (GaloisField p f) γ ⊔ rootSubgroup τ (GaloisField p f) (-γ) := by
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have : Finite (ModGL τ (GaloisField p f)) := finite_modGL
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  obtain ⟨g, b, hb, hgz⟩ := exists_conj_eq_rootDiagUnit_of_involution hτ hodd z hz2
  have hL' := isClassicalMember_map_conj hodd h g
  obtain ⟨γ, hγ, h1, h2⟩ := exists_eq_rankOne_of_isClassicalMember_toral hp2 hq b hb hgz hL'
  refine ⟨g, b, γ, hγ, ?_, h2⟩
  have hL'eq := eq_rootGroup_sup_of_map_eq (rootOperatorFamily τ) hγ.1 (h1.trans h2)
  rw [← hL'eq, Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply]
  constructor
  · intro hx
    exact ⟨x, hx, by group⟩
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    group

end Core

theorem isLongestRoot_of_mem_roots_of_forall_single {K : Type*} [Group K]
    (D : UniversalRootDatum K) (hdiv : D.divisible = ∅)
    (hlong : ∀ k : Fin D.rank, IsLongestRoot D (Pi.single k 1)) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : IsLongestRoot D γ := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · exact (hlong i).map_weylAction w
  · rw [hdiv] at hi
    exact absurd hi (Set.notMem_empty i)

section Tags

variable {p f : ℕ} [Fact p.Prime]

theorem classicalMembersFundamental_g2 {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ClassicalMembersFundamental p f .G2 n f hp := by
  intro L z hL
  obtain ⟨g, b, γ, hγ, hLeq, -⟩ := exists_conj_eq_rootGroup_sup_of_isClassicalMember
    (τ := .G2) (Or.inl rfl) hp2 hq hL
  exact ⟨g⁻¹, γ, Or.inr (Or.inl ⟨rfl, mem_adjDatum_roots.2 hγ.1⟩), hLeq⟩

theorem classicalMembersFundamental_e8 {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .E8 n p f) : ClassicalMembersFundamental p f .E8 n f hp := by
  intro L z hL
  obtain ⟨g, b, γ, hγ, hLeq, -⟩ := exists_conj_eq_rootGroup_sup_of_isClassicalMember
    (τ := .E8) (Or.inr (Or.inr (Or.inr rfl))) hp2 hq hL
  have hlong := isLongestRoot_single .E8 n p f hp trivial hadm
  exact ⟨g⁻¹, γ, Or.inl (isLongestRoot_of_mem_roots_of_forall_single _ rfl
    (fun k => hlong k trivial) (mem_adjDatum_roots.2 hγ.1)), hLeq⟩

end Tags


end CFSG.ClassicalInvolution.ModelFacts
