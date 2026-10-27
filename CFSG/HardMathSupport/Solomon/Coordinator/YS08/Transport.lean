module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3K
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem i253α_pow_three_of_cube_mem_centralizer {Y : Type*} [Group Y] (K : Subgroup Y) {b : Y}
    (hb : b ∈ Subgroup.normalizer (K : Set Y)) (hb3 : b ^ 3 ∈ Subgroup.centralizer (K : Set Y)) :
    i253α K b hb ^ 3 = 1 := by
  ext k
  have h1 : ((i253α K b hb ^ 3) k : Y) = b ^ 3 * k * (b ^ 3)⁻¹ := by
    have : (i253α K b hb ^ 3 : MulAut ↥K) = K.normalizerMonoidHom (⟨b, hb⟩ ^ 3) := by
      unfold i253α; rw [map_pow]
    rw [this]
    rfl
  rw [MulAut.one_apply, h1]
  have := Subgroup.mem_centralizer_iff.1 hb3 (k : Y) k.2
  calc b ^ 3 * (k : Y) * (b ^ 3)⁻¹ = (k : Y) * b ^ 3 * (b ^ 3)⁻¹ := by rw [← this]
    _ = (k : Y) := by group

theorem barEquiv_of_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (e : A ≃* B) :
    Nonempty ((A ⧸ GLAPPrimeCore 3 A) ≃* (B ⧸ GLAPPrimeCore 3 B)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (GLAPPrimeCore 3 A).map e.toMonoidHom ≤ GLAPPrimeCore 3 B :=
    CFSG.map_pPrimeCore_le e.toMonoidHom e.surjective
  have h2 : (GLAPPrimeCore 3 B).map e.symm.toMonoidHom ≤ GLAPPrimeCore 3 A :=
    CFSG.map_pPrimeCore_le e.symm.toMonoidHom e.symm.surjective
  have hmap : (GLAPPrimeCore 3 A).map e.toMonoidHom = GLAPPrimeCore 3 B := by
    refine le_antisymm h1 ?_
    intro y hy
    refine ⟨e.symm y, h2 ⟨y, hy, rfl⟩, ?_⟩
    simp
  exact ⟨QuotientGroup.congr (GLAPPrimeCore 3 A) (GLAPPrimeCore 3 B) e hmap⟩

theorem component_to_aut {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) {b : Y}
    (hb : b ∈ Subgroup.normalizer (K : Set Y)) (hb3 : b ^ 3 ∈ Subgroup.centralizer (K : Set Y))
    {J : Subgroup Y} (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) J) :
    ∃ (α : MulAut ↥K) (J' : Subgroup ↥K), α ^ 3 = 1 ∧
      GLAPComponent 3 (Lemma510Ns.fixSub α) J' ∧ Nonempty (barOf 3 J' ≃* barOf 3 J) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  refine ⟨i253α K b hb, ?_⟩
  have hX : (fixSubgroup (i253α K b hb)).map K.subtype = K ⊓ Subgroup.centralizer ({b} : Set Y) :=
    map_fixSubgroup_i253α K b hb
  have hc : ∀ y ∈ fixSubgroup (i253α K b hb) ⊓ K.subtype.ker, ∀ z ∈ fixSubgroup (i253α K b hb),
      z * y = y * z := by
    intro y hy z _
    have : y = 1 := Subtype.ext (MonoidHom.mem_ker.1 hy.2)
    rw [this, mul_one, one_mul]
  obtain ⟨J', hJ', hmap⟩ := exists_glaPComponent_map_central hp K.subtype hc (hX ▸ hJ)
  refine ⟨J', i253α_pow_three_of_cube_mem_centralizer K hb hb3, hJ', ?_⟩
  subst hmap
  exact barEquiv_of_mulEquiv (J'.equivMapOfInjective K.subtype K.subtype_injective)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
