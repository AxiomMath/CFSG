module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthD4Reduce
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3FamilyD
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3QPlus
public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneD4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Residual
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne
  CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCOrthogonal

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section Planes

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem innerPlanesBalanced_projOrth3 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (hrig : ∀ A : Subgroup (ProjOrthDerived Q), IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∀ g : MulAut (ProjOrthDerived Q),
        (∀ a ∈ A, a ≠ 1 → ∀ n ∈ ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
          Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆, g n = n) → g = 1) :
    InnerPlanesBalanced p (ProjOrthDerived Q) := by
  intro E hEin hEel hEc H hH
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
  set E₁ : Subgroup (ProjOrthDerived Q) :=
    E.comap (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) with hE₁
  have hmap : E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) = E :=
    Subgroup.map_comap_eq_self hEin
  have hE₁el : IsElemAbelian p E₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have h2 : MulAut.conj (a : ProjOrthDerived Q) * MulAut.conj (b : ProjOrthDerived Q) =
          MulAut.conj (b : ProjOrthDerived Q) * MulAut.conj (a : ProjOrthDerived Q) :=
        congrArg Subtype.val (hEel.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact h2
    · rw [map_pow, map_one]
      exact hEel.2 _ hx
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hEc]
  have hbot := localDeltaIn_eq_bot_projOrth3 hQ hT hp hp2 hK4 hpl E₁ hE₁el hE₁c
    (hrig E₁ hE₁el hE₁c) hH
  rwa [hmap] at hbot

theorem orth3_qplus_derived_rigid_of_natural
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (hpq : p ∣ Nat.card K + 1)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2)
    (hnat : ∀ α : MulAut (ProjOrthDerived Q),
      (∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥((MulAut.conj : ProjOrthDerived Q →*
          MulAut (ProjOrthDerived Q)).range ⊓ Subgroup.centralizer
          ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
        α * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * α) →
      KCOrthogonalAut.InducedBySemilinear Q α)
    (g : MulAut (ProjOrthDerived Q))
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
    hAcard hnat
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

end Planes

section D4

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem d4_qplus_derived_rigid (Gm : Type) [Group Gm] {ℓ f : ℕ}
    (h : StatedClassicalModel Gm .POmegaPlus 4 ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : Gm ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) (hpl : p ≠ ringChar K)
    (hpq : p ∣ Nat.card K + 1)
    (A : Subgroup (ProjOrthDerived (coordinateQuadPlus 4 K))) (hA : Assembly.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (g : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)))
    (hg : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ ⁅Subgroup.centralizer
        ({a} : Set (ProjOrthDerived (coordinateQuadPlus 4 K))),
        Subgroup.centralizer ({a} : Set (ProjOrthDerived (coordinateQuadPlus 4 K)))⁆,
        g n = n) : g = 1 := by
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  refine orth3_qplus_derived_rigid_of_natural hnd hT hp hp2 hK4 hpl hpq A hA hAcard
    (fun α hcent => ?_) g hg
  obtain ⟨u, v, hgu, hu, hv, huv, hind, -, heich, hfix⟩ :=
    qplus_pair_involution3 hnd hT hp hp2 hK4 hpl hpq
      (MulAut.conj : ProjOrthDerived (coordinateQuadPlus 4 K) →*
        MulAut (ProjOrthDerived (coordinateQuadPlus 4 K))).range le_rfl A hA hAcard α hcent
  exact d4_induced_of_fixes_involution Gm h K hK e α hu hv huv hind hgu heich hfix

end D4

end CFSG.HardMathSupport.Timmesfeld.CrossChar
