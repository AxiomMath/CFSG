module

public import CFSG.Goldschmidt75.TheoremBcBasic
public import CFSG.Goldschmidt75.Local

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem localRc_of_lt (P : Sylow p G) {S S₀ : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) (hS₀ : S₀ ≤ S) (hfn : FullyNormalized p P S₀)
    (hL : RcFor p (normalizer (S₀ : Set G)))
    (hlarger : LocalRc S P (S ⊓ normalizer (S₀ : Set G))) : LocalRc S P S₀ := by
  intro h hh x hx hxh
  set L := normalizer (S₀ : Set G)
  set S₁ := S ⊓ L
  have hcard := card_inf_normalizer hfn
  set PL := sylowOfInf P L hcard
  have hSL := stronglyClosed_inf_subgroupOf P hS L hcard
  have hSLP := inf_subgroupOf_le_sylowOfInf P hSP L hcard
  have hRL := hL PL (S₁.subgroupOf L) hSLP hSL
  have hCL : centralizer (S : Set G) ≤ L := centralizer_le_normalizer_of_le hS₀
  have hxL : x ∈ L := hCL (rcSet_le_centralizer S P hx)
  have hCS₁ : centralizer (S : Set G) ≤ centralizer (S₁ : Set G) :=
    Subgroup.centralizer_le fun y hy => hy.1
  have hx' : (⟨x, hxL⟩ : L) ∈ rcSet (S₁.subgroupOf L) PL := by
    refine ⟨?_, mem_sylowOfInf.2 (rcSet_le S P hx)⟩
    have h1 := mem_commutator_subgroupOf hCL hx.1 hxL
    have h2 : (centralizer (S : Set G)).subgroupOf L ≤
        centralizer ((S₁.subgroupOf L : Subgroup L) : Set L) :=
      fun y hy => (mem_centralizer_subgroupOf_iff (inf_le_right : S₁ ≤ L)).2 (hCS₁ hy)
    exact Subgroup.commutator_mono h2 h2 h1
  have hh' : (⟨h, hh⟩ : L)⁻¹ * ⟨x, hxL⟩ * ⟨h, hh⟩ ∈ (PL : Subgroup L) :=
    mem_sylowOfInf.2 (by simpa using hxh)
  have h3 := hRL _ hx' ⟨h, hh⟩ hh'
  have hxhC : h⁻¹ * x * h ∈ centralizer (S₁ : Set G) := by
    have := (mem_centralizer_subgroupOf_iff (inf_le_right : S₁ ≤ L)).1
      (rcSet_le_centralizer _ _ h3)
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at this
  have hxC : x ∈ centralizer (S₁ : Set G) := hCS₁ (rcSet_le_centralizer S P hx)
  obtain ⟨m, hm, hmeq⟩ :=
    exists_normalizer_conj_of_le PL inf_le_right hSLP hSL hxL hh hxC hxhC
  rw [← hmeq]
  exact hlarger m hm.2 x hx (by rw [hmeq]; exact hxh)

end CFSG.Goldschmidt75
