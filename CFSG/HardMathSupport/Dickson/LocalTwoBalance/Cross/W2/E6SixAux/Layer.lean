module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6SixAux.Order
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE6.Phi6Core

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective adjEmb_mem
  adjEmb_frobenius twistedFixedPoints mem_twistedFixedPoints)
open scoped Matrix MatrixGroups Pointwise commutatorElement

theorem e6_six_layer (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * phi6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E6 K L).range)
    {x : adjointGroup Tag.E6 K} (hxp : orderOf x = p)
    (hh : g0⁻¹ * adjEmb Tag.E6 K L x * g0 ∈
      twistedTorus (phi6N L) (iterateFrobenius L ℓ f))
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel (g0⁻¹ * adjEmb Tag.E6 K L x * g0) =
        parabolicRoots Tag.E6 supportA2A2) :
    CFSG.IsQuasisimple ↥((CFSG.perfectResidual (Subgroup.centralizer ({x} :
      Set (adjointGroup Tag.E6 K)))).map (Subgroup.centralizer ({x} :
        Set (adjointGroup Tag.E6 K))).subtype) ∧
    ¬ Nat.Coprime p (Nat.card ↥((CFSG.perfectResidual (Subgroup.centralizer ({x} :
      Set (adjointGroup Tag.E6 K)))).map (Subgroup.centralizer ({x} :
        Set (adjointGroup Tag.E6 K))).subtype)) ∧
    ∀ a : Fin Tag.E6.rank → Lˣ,
      (∀ d ∈ (CFSG.perfectResidual (Subgroup.centralizer ({x} :
          Set (adjointGroup Tag.E6 K)))).map (Subgroup.centralizer ({x} :
            Set (adjointGroup Tag.E6 K))).subtype,
        rootDiagUnit Tag.E6 a * (g0⁻¹ * adjEmb Tag.E6 K L d * g0) =
          (g0⁻¹ * adjEmb Tag.E6 K L d * g0) * rootDiagUnit Tag.E6 a) →
      ∀ α ∈ torusRootKernel (g0⁻¹ * adjEmb Tag.E6 K L x * g0), rootChar a α = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr c
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hpq' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    rw [hK] at hpq
    exact hpq
  set ι : adjointGroup Tag.E6 K →* ModGL Tag.E6 L := adjEmb Tag.E6 K L with hιdef
  set y : ModGL Tag.E6 L := g0⁻¹ * ι x * g0 with hydef
  have hyH : y ∈ torusGroup Tag.E6 L := (mem_twistedTorus.1 hh).1
  have hordy : orderOf y = p := by
    have e1 : orderOf y = orderOf (ι x) := by
      have := orderOf_injective (MulAut.conj g0⁻¹).toMonoidHom (MulAut.conj g0⁻¹).injective (ι x)
      rw [hydef]
      simpa [MulAut.conj_apply] using this
    rw [e1, orderOf_injective ι adjEmb_injective x, hxp]
  set D : Subgroup (adjointGroup Tag.E6 K) := Subgroup.centralizer ({x} :
    Set (adjointGroup Tag.E6 K)) with hD
  obtain ⟨ψ, hψinj, hψdef, hψHQ, hψfix, hPψ, hPq, hC6⟩ := phi6_embedding_A2A2 K hf hK hp hp3 hpq L
    hg0C hg0 hperf hxp hh hA2A2
  set P : Subgroup (ModGL Tag.E6 L) := phi6P L Fr (torusRootKernel y) with hPdef
  have hHN : torusGroup Tag.E6 L ≤
      Subgroup.normalizer (rootSpan Tag.E6 L (torusRootKernel y) : Set (ModGL Tag.E6 L)) :=
    CFSG.RankThree.Classical2.torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have hcomm := commutator_sup_le_of_comm (torusGroup_comm (Ω := L)) hHN
  have hψR : ψ.range ≤ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (torusRootKernel y) := by
    rintro _ ⟨d, rfl⟩
    exact hψHQ d
  have hc1 : ⁅ψ.range, ψ.range⁆ ≤ phi6Qθ L Fr (torusRootKernel y) := by
    refine le_inf ((Subgroup.commutator_mono hψR hψR).trans hcomm) ?_
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨da, rfl⟩ := ha
    obtain ⟨db, rfl⟩ := hb
    show phi6Theta L Fr ⁅ψ da, ψ db⁆ = ⁅ψ da, ψ db⁆
    have h1 : phi6Theta L Fr (ψ da) = ψ da := hψfix da
    have h2 : phi6Theta L Fr (ψ db) = ψ db := hψfix db
    rw [map_commutatorElement, h1, h2]
  have hD2 : ⁅⁅ψ.range, ψ.range⁆, ⁅ψ.range, ψ.range⁆⁆ ≤ P := Subgroup.commutator_mono hc1 hc1
  have hPperf : ⁅P, P⁆ = P := by
    exact Subgroup.isPerfect_iff.1 hPq.1
  have hmapD : (CFSG.perfectResidual D).map ψ = P :=
    perfectResidual_map_eq ψ hψinj P hPψ hPperf hD2
  have hDq : CFSG.IsQuasisimple ↥((CFSG.perfectResidual D).map D.subtype) :=
    isQuasisimple_perfectResidual D ψ hψinj P hPq hmapD
  refine ⟨hDq, ?_, fun a ha α hα => ?_⟩
  · have hcardD : Nat.card ↥((CFSG.perfectResidual D).map D.subtype) = Nat.card P := by
      rw [Subgroup.card_map_of_injective D.subtype_injective, ← hmapD,
        Subgroup.card_map_of_injective hψinj]
    rw [hcardD]
    exact e6_six_p_dvd_card_P (K := K) hℓ hf hK hFr hp hp3 hpq' hh hordy hA2A2
  · obtain ⟨-, -, -, -, -, -, hcentQ⟩ := phi6_A2A2_case (K := K) hℓ hf hK hFr hp hp3 hpq' hh hordy
      hA2A2
    have hG : rootDiagUnit Tag.E6 a ∈ torusGroup Tag.E6 L := rootDiagUnit_mem_torusGroup a
    have hcP : ∀ u ∈ P, rootDiagUnit Tag.E6 a * u = u * rootDiagUnit Tag.E6 a := by
      intro u hu
      rw [← hmapD] at hu
      obtain ⟨d', hd', rfl⟩ := hu
      have hd'D : (d' : adjointGroup Tag.E6 K) ∈ (CFSG.perfectResidual D).map D.subtype :=
        ⟨d', hd', rfl⟩
      rw [hψdef d']
      exact ha _ hd'D
    have hcent := hcentQ _ hG hcP
    exact CFSG.RankThree.PartOne.KE.rootChar_eq_one_of_centralizes hα.1 hα
      (Subgroup.mem_centralizer_iff.2 fun g hg => (hcent g hg).symm)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
