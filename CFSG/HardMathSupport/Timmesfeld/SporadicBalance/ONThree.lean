module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowONan
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.AGLEmbedding CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance

variable {X : Type} [Group X] {p : ℕ}

theorem isElemAbelian_span (D : ModuleSpec X p) : IsElemAbelian p D.span := by
  have hgen : ∀ i j, D.a i ∈ Subgroup.centralizer ({D.a j} : Set X) := fun i j =>
    Subgroup.mem_centralizer_singleton_iff.2 (D.comm i j)
  have hspan : ∀ j, D.span ≤ Subgroup.centralizer ({D.a j} : Set X) := fun j => by
    rw [ModuleSpec.span, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hgen i j
  have hcomm : ∀ x ∈ D.span, ∀ y ∈ D.span, x * y = y * x := by
    intro x hx y hy
    have hy' : y ∈ Subgroup.centralizer (D.span : Set X) := by
      have : D.span ≤ Subgroup.centralizer (D.span : Set X) := by
        rw [ModuleSpec.span, Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        intro z hz
        exact Subgroup.mem_centralizer_singleton_iff.1 (hspan i hz)
      exact this hy
    exact Subgroup.mem_centralizer_iff.1 hy' x hx
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact D.pow i
  | one => simp
  | mul y z hy hz hy1 hz1 =>
    have hc := hcomm y hy z hz
    rw [(Commute.mul_pow hc p : (y * z) ^ p = y ^ p * z ^ p), hy1, hz1, one_mul]
  | inv y hy hy1 => rw [inv_pow, hy1, inv_one]

theorem exists_sylow_elemAbelian_of_moduleSpec [Finite X] (hp : p.Prime) (D : ModuleSpec X p)
    (hidx : ¬ p ∣ D.span.index) : ∃ T : Sylow p X, IsElemAbelian p (T : Subgroup X) := by
  have hE := isElemAbelian_span D
  have : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p D.span := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  exact ⟨hP.toSylow hidx, hE⟩

theorem exists_sylow_elemAbelian_ON
    (S : Type) [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .ONan) :
    ∃ T : Sylow 3 S, IsElemAbelian 3 (T : Subgroup S) := by
  obtain ⟨D, -, -, -, hidx⟩ := abelianSylowDatum_ON_three
  have e0 : S ≃* NativeSporadic.ON := e
  have hf : Function.Injective (e0.symm : NativeSporadic.ON →* S) := e0.symm.injective
  refine exists_sylow_elemAbelian_of_moduleSpec Nat.prime_three (D.map (e0.symm : _ →* S) hf) ?_
  rw [ModuleSpec.map_span, Subgroup.index_map_equiv]
  exact hidx

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
