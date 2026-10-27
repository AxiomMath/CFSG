module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3KCQPlusOne
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Plane
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth3_layer_inner_le (hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q))) (a : ProjOrthDerived Q) :
    (CFSG.layer ↥(Inn (ProjOrthDerived Q) ⊓
      Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
      (Inn (ProjOrthDerived Q) ⊓
        Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype ≤
    (⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆).map
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) := by
  set S : Subgroup (MulAut (ProjOrthDerived Q)) := Inn (ProjOrthDerived Q) ⊓
    Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))) with hS
  have hSeq : S = (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))).map
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) := by
    ext φ
    rw [hS, Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨⟨k, rfl⟩, hk⟩
      refine ⟨k, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
      apply hinj
      rw [map_mul, map_mul]
      exact hk
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨k, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
      rw [← map_mul, ← map_mul, hk]
  have h1 : (CFSG.layer ↥S).map S.subtype ≤ ⁅S, S⁆ := by
    refine (Subgroup.map_mono (layer_le_commutator_top_orth ↥S)).trans ?_
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  refine h1.trans ?_
  rw [hSeq, ← Subgroup.map_commutator]

theorem orth3_qplus_derived_rigid
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (hpq : p ∣ Nat.card K + 1)
    (hnat : ∀ α : MulAut (ProjOrthDerived Q), KCOrthogonalAut.InducedBySemilinear Q α)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (g : MulAut (ProjOrthDerived Q))
    (hg : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
        Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆, g n = n) : g = 1 := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj := conj_injective_of_center_eq_bot_orth hcenter
  have hbot := orthogonal_inner_plane_common_centralizer_q_plus_one_of_natural3 Q hQ hT hp hp2
    hK4 hpl hpq (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range le_rfl A hA
    hAcard (fun α _ => hnat α)
  have hmem : g ∈ (⨅ (a : ProjOrthDerived Q) (_ : a ∈ A ∧ a ≠ 1),
      Subgroup.centralizer (((CFSG.layer ↥((MulAut.conj : ProjOrthDerived Q →*
          MulAut (ProjOrthDerived Q)).range ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
        ((MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ⊓
          Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype :
          Subgroup (MulAut (ProjOrthDerived Q))) : Set (MulAut (ProjOrthDerived Q)))) := by
    rw [Subgroup.mem_iInf]
    intro a
    rw [Subgroup.mem_iInf]
    rintro ⟨haA, ha1⟩
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' := orth3_layer_inner_le hinj a hd
    obtain ⟨n, hn, rfl⟩ := hd'
    have hgn : g n = n := hg a haA ha1 n hn
    have h1 := mul_conj_mul_inv g n
    rw [hgn] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

end CFSG.HardMathSupport.Timmesfeld.CrossChar
