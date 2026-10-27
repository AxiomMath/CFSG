module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.GroupTheory

theorem pCore_le_pPrimeCore {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (G : Type*) [Group G] [Finite G] :
    CFSG.pCore p G ≤ CFSG.pPrimeCore q G := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := ↥(CFSG.pCore p G))).mp
    (CFSG.pCore_isPGroup (p := p) (G := G))
  refine le_sSup ⟨CFSG.pCore_normal (p := p) (G := G), ?_⟩
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq))

theorem pPrimeCore_le_pCore_of_simple_quotient {D : Type} [Group D] {H : Type*} [Group H]
    [IsSimpleGroup H] (e : (D ⧸ CFSG.pCore 2 D) ≃* H)
    (hne : CFSG.pPrimeCore 3 D ≠ ⊤) (hO2 : CFSG.pCore 2 D ≤ CFSG.pPrimeCore 3 D) :
    CFSG.pPrimeCore 3 D ≤ CFSG.pCore 2 D := by
  let π := QuotientGroup.mk' (CFSG.pCore 2 D)
  let N : Subgroup (D ⧸ CFSG.pCore 2 D) := Subgroup.map π (CFSG.pPrimeCore 3 D)
  have hN : N.Normal :=
    Subgroup.Normal.map (CFSG.pPrimeCore_normal (p := 3)) π (QuotientGroup.mk'_surjective _)
  have hN' : (Subgroup.map e.toMonoidHom N).Normal := hN.map e.toMonoidHom e.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.map e.toMonoidHom N) with hbot | htop
  · have hNbot : N = ⊥ := by
      rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hbot
      exact hbot
    rw [show N = Subgroup.map π (CFSG.pPrimeCore 3 D) from rfl, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk'] at hNbot
    exact hNbot
  · exfalso
    have hNtop : N = ⊤ := by
      have h := congrArg (Subgroup.map e.symm.toMonoidHom) htop
      have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom =
          MonoidHom.id (D ⧸ CFSG.pCore 2 D) := by
        ext x
        simp
      rwa [Subgroup.map_map, hcomp, Subgroup.map_id,
        Subgroup.map_top_of_surjective _ e.symm.surjective] at h
    apply hne
    have h1 : Subgroup.comap π N = ⊤ := by rw [hNtop, Subgroup.comap_top]
    rw [show N = Subgroup.map π (CFSG.pPrimeCore 3 D) from rfl, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk', sup_eq_left.mpr hO2] at h1
    exact h1

theorem center_le_of_quotient_simple {Q : Type*} [Group Q] (R : Subgroup Q) [R.Normal]
    (hsimple : IsSimpleGroup (Q ⧸ R)) (hnc : ¬ IsMulCommutative (Q ⧸ R)) :
    Subgroup.center Q ≤ R := by
  intro z hz
  by_contra hzR
  have hzq : QuotientGroup.mk' R z ∈ Subgroup.center (Q ⧸ R) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R y
    simpa only [map_mul] using congrArg (QuotientGroup.mk' R)
      (Subgroup.mem_center_iff.mp hz y)
  have hne : Subgroup.center (Q ⧸ R) ≠ ⊤ := fun h =>
    hnc (Subgroup.center_eq_top_iff.mp h)
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ R)) with h | h
  · have hz1 : QuotientGroup.mk' R z = 1 := by
      rw [h] at hzq
      simpa using hzq
    exact hzR ((QuotientGroup.eq_one_iff z).mp hz1)
  · exact hne h

end CFSG.GroupTheory

end
