module

public import CFSG.RankThree.PartOne.KGD.D4QFrame

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD
open scoped Matrix Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem ap_plane_elements {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [CharP L ℓ]
    [IsAlgClosed L] {K : Type} [Field K] {σ : K ≃+* K} [Algebra K L] (hq : (ℓ ^ f) % 3 = 2)
    {g0 : ModGL TwistTag.D4.tag L}
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hEcard : Nat.card E = 3 ^ 2)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hEψ : ∀ e ∈ E, g0⁻¹ * triEmb K σ L e * g0 ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    ∃ ω : Lˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ∃ xA ∈ E, ∃ xB ∈ E,
      rootDiagUnit TwistTag.D4.tag ![ω, ω, 1, ω] = g0⁻¹ * triEmb K σ L xA * g0 ∧
      rootDiagUnit TwistTag.D4.tag ![1, 1, ω, 1] = g0⁻¹ * triEmb K σ L xB * g0 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hpq : 3 ∣ ℓ ^ f + 1 := by omega
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.D4.tag L) := rootDiagUnit_injective
  let φ : E →* ModGL TwistTag.D4.tag L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ((triEmb K σ L).comp E.subtype)
  have hφ : ∀ q : E, φ q = g0⁻¹ * triEmb K σ L q * g0 := fun q => by
    change (MulAut.conj g0⁻¹ : MulAut (ModGL TwistTag.D4.tag L))
      (triEmb K σ L (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hφinj : Function.Injective φ := by
    intro q q' h
    rw [hφ, hφ] at h
    have h1 : g0⁻¹ * triEmb K σ L (q : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
        g0⁻¹ * triEmb K σ L (q' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      mul_right_cancel h
    exact Subtype.ext (triEmb_injective (mul_left_cancel h1))
  have hφT : ∀ q : E, φ q ∈ twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L Fr) :=
    fun q => by
      rw [hφ]
      exact hEψ q q.2
  choose a ha using fun q : E =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin TwistTag.D4.tag.rank → Lˣ, φ q = rootDiagUnit TwistTag.D4.tag b)
  have hafix : ∀ q : E, a q ∈ fixedCharTuples d4QM Fr := fun q => by
    have h := hφT q
    rw [d4Q_twistedTorus, ha q] at h
    obtain ⟨a', ha', haa'⟩ := h
    have : a' = a q := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) haa'
    exact this ▸ ha'
  have hamul : ∀ q q' : E, a (q * q') = a q * a q' := fun q q' => by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    rw [← ha, rootDiagUnit_mul, ← ha, ← ha, map_mul]
  have haone : a 1 = 1 := by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    rw [← ha, map_one, rootDiagUnit_one]
  have ha3 : ∀ q : E, ∀ i, a q i ^ 3 = 1 := fun q i => by
    have h1 : rootDiagUnit TwistTag.D4.tag (a q) ^ 3 = 1 := by
      rw [← ha, ← map_pow]
      have : q ^ 3 = 1 := Subtype.ext (hE3 q q.2)
      rw [this, map_one]
    have h2 : a q ^ 3 = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  have hform : ∀ q : E, a q = ![a q 0, a q 0, a q 2, a q 0] := fun q => by
    obtain ⟨h1, h3⟩ := d4Q_eq_of_pow_eq_one hFr hpq (hafix q) (ha3 q)
    funext i
    fin_cases i
    · rfl
    · exact h1
    · rfl
    · exact h3
  let π : E → rootsOfUnity 3 L × rootsOfUnity 3 L := fun q =>
    (⟨a q 0, (mem_rootsOfUnity _ _).2 (ha3 q 0)⟩, ⟨a q 2, (mem_rootsOfUnity _ _).2 (ha3 q 2)⟩)
  have hπinj : Function.Injective π := by
    intro q q' h
    have h0 : a q 0 = a q' 0 := congrArg (fun p => (p.1 : Lˣ)) h
    have h2 : a q 2 = a q' 2 := congrArg (fun p => (p.2 : Lˣ)) h
    apply hφinj
    rw [ha q, ha q', hform q, hform q', h0, h2]
  have hR3 : Nat.card (rootsOfUnity 3 L) ≤ 3 := card_rootsOfUnity L 3
  have hfinE : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  have hEπ : Nat.card E ≤ Nat.card (rootsOfUnity 3 L × rootsOfUnity 3 L) :=
    Nat.card_le_card_of_injective π hπinj
  rw [Nat.card_prod, hEcard] at hEπ
  have hR3eq : Nat.card (rootsOfUnity 3 L) = 3 := by
    generalize Nat.card (rootsOfUnity 3 L) = c at hEπ hR3 ⊢
    interval_cases c <;> omega
  have hbij : Function.Bijective π := hπinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, hR3eq, hEcard]
    norm_num)
  obtain ⟨ω, hω1⟩ : ∃ ω : rootsOfUnity 3 L, ω ≠ 1 := by
    have : Nontrivial (rootsOfUnity 3 L) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    exact exists_ne 1
  obtain ⟨xA, hxA⟩ := hbij.2 (ω, 1)
  obtain ⟨xB, hxB⟩ := hbij.2 (1, ω)
  have hxA0 : a xA 0 = ω := congrArg (fun p => (p.1 : Lˣ)) hxA
  have hxA2 : a xA 2 = 1 := congrArg (fun p => (p.2 : Lˣ)) hxA
  have hxB0 : a xB 0 = 1 := congrArg (fun p => (p.1 : Lˣ)) hxB
  have hxB2 : a xB 2 = ω := congrArg (fun p => (p.2 : Lˣ)) hxB
  refine ⟨ω, (mem_rootsOfUnity _ _).1 ω.2, fun h => hω1 (Subtype.ext h), xA, xA.2, xB, xB.2, ?_, ?_⟩
  · rw [← hφ, ha xA, hform xA, hxA0, hxA2]
  · rw [← hφ, ha xB, hform xB, hxB0, hxB2]



end CFSG.GH74.GLS.Stage2.Bender.Thm1
