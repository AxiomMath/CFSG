module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rational
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcSigns
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcReduce

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank

section StdRankOne

variable {K : Type} [Field K]

theorem mem_stdRankOne_e8_iff (r : ↥(adjointGroup .E8 K)) :
    r ∈ stdRankOne (e8Datum K) thetaE8 ↔
      ∃ A : SL2 K, (r : ModGL .E8 K) = rootSL2 .E8 K thetaE8 A := by
  have hb := subgroupOf_rootSubgroup_sup_eq (K := K) (rootOperatorFamily .E8) isRoot_thetaE8
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E8 K isRoot_thetaE8).1
  change r ∈ rootGroup (rootOperatorFamily .E8) K thetaE8 ⊔
    rootGroup (rootOperatorFamily .E8) K (-thetaE8) ↔ _
  rw [← hb, Subgroup.mem_subgroupOf, ← hL, rootRankOneGroup, MonoidHom.mem_range]
  exact exists_congr fun A => eq_comm

theorem central_stdRankOne_e8 (hK : ringChar K ≠ 2) {z : ↥(adjointGroup .E8 K)}
    (hz : z ∈ stdRankOne (e8Datum K) thetaE8)
    (hzc : ∀ r ∈ stdRankOne (e8Datum K) thetaE8, z * r = r * z) :
    (z : ModGL .E8 K) = 1 ∨
      (z : ModGL .E8 K) = rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : Kˣ)) := by
  obtain ⟨A, hA⟩ := (mem_stdRankOne_e8_iff z).1 hz
  have hinj : Function.Injective (rootSL2 .E8 K thetaE8) :=
    ((exceptional_Lang_root_rank_one_data .E8 K thetaE8).2.2.2.2.2.2.2.1 hK).1
  have hcomm : ∀ B : SL2 K, A * B = B * A := fun B => by
    apply hinj
    have hB : (⟨rootSL2 .E8 K thetaE8 B, rootSL2_mem_adjointGroup _ _⟩ : ↥(adjointGroup .E8 K)) ∈
        stdRankOne (e8Datum K) thetaE8 := (mem_stdRankOne_e8_iff _).2 ⟨B, rfl⟩
    have := congrArg Subtype.val (hzc _ hB)
    simp only [Subgroup.coe_mul] at this
    rw [hA] at this
    rw [map_mul, map_mul]
    exact this
  rcases eq_one_or_HSL_neg_one_of_forall_commute hcomm with h | h
  · left
    rw [hA, h, map_one]
  · right
    rw [hA, h]
    exact rootTorusSL2_thetaE8 (-1)

end StdRankOne

section Model

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

theorem odd_natCard_galoisField_of_ne_two (hp2 : p ≠ 2) : Odd (Nat.card (GaloisField p e)) := by
  rw [GaloisField.card p e (NeZero.ne e)]
  exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow

theorem rootDiagUnit_thetaDiag_mul_self {F : Type} [Field F] (δ : Fin (Tag.rank .E8) → ℤ) :
    rootDiagUnit .E8 (thetaDiag δ (-1 : Fˣ)) * rootDiagUnit .E8 (thetaDiag δ (-1 : Fˣ)) = 1 := by
  rw [← rootDiagUnit_mul, ← rootDiagUnit_one]
  congr 1
  funext i
  rcases thetaDiag_neg_one_sign (F := F) δ i with h | h <;> simp [h]

theorem mem_excSignGroup_e8 {u : ↥(adjointGroup .E8 (GaloisField p e))} (δ : Fin (Tag.rank .E8) → ℤ)
    (hu : (u : ModGL .E8 (GaloisField p e)) =
      rootDiagUnit .E8 (thetaDiag δ (-1 : (GaloisField p e)ˣ))) : u ∈ excSignGroup .E8 p e :=
  mem_excSignGroup.2 ⟨thetaDiag δ (-1), thetaDiag_neg_one_sign δ, hu⟩

theorem hZ_e8 (hp2 : p ≠ 2) :
    ∀ c ∈ stdRankOne (e8Datum (GaloisField p e)) thetaE8,
      (∀ r ∈ stdRankOne (e8Datum (GaloisField p e)) thetaE8, c * r = r * c) →
        c ∈ excSignGroup .E8 p e ∧ c * c = 1 := by
  intro c hc hcc
  rcases central_stdRankOne_e8 (ringChar_galoisField_ne_two hp2) hc hcc with h | h
  · have h1 : c = 1 := Subtype.ext h
    rw [h1]
    exact ⟨one_mem _, mul_one _⟩
  · refine ⟨mem_excSignGroup_e8 thetaE8 h, Subtype.ext ?_⟩
    change (c : ModGL .E8 (GaloisField p e)) * (c : ModGL .E8 (GaloisField p e)) = 1
    rw [h]
    exact rootDiagUnit_thetaDiag_mul_self thetaE8

theorem hbase_e8 (hp2 : p ≠ 2) :
    ∀ c : ↥(adjointGroup .E8 (GaloisField p e)),
      (∀ r ∈ stdRankOne (e8Datum (GaloisField p e)) thetaE8, c * r = r * c) → c * c = 1 →
      (∃ g z : ↥(adjointGroup .E8 (GaloisField p e)),
        z ∈ stdRankOne (e8Datum (GaloisField p e)) thetaE8 ∧
        (∀ r ∈ stdRankOne (e8Datum (GaloisField p e)) thetaE8, z * r = r * z) ∧
        c = g * z * g⁻¹) →
      ∃ x : ↥(adjointGroup .E8 (GaloisField p e)),
        (∀ z ∈ stdRankOne (e8Datum (GaloisField p e)) thetaE8,
          (∀ r ∈ stdRankOne (e8Datum (GaloisField p e)) thetaE8, z * r = r * z) →
            x * z = z * x) ∧
        x * c * x⁻¹ ∈ excSignGroup .E8 p e := by
  intro c hcR hc2 ⟨g, z, hz, hzc, hcg⟩
  have hK : ringChar (GaloisField p e) ≠ 2 := ringChar_galoisField_ne_two hp2
  have hKodd := odd_natCard_galoisField_of_ne_two (p := p) (e := e) hp2
  rcases central_stdRankOne_e8 hK hz hzc with hz1 | hzd
  ·
    have hc1 : c = 1 := by
      rw [hcg, show z = 1 from Subtype.ext hz1]
      group
    refine ⟨1, fun z' _ _ => by simp, ?_⟩
    rw [hc1, one_mul, inv_one, mul_one]
    exact one_mem _
  · have hcom : ∀ B : SL2 (GaloisField p e),
        (c : ModGL .E8 (GaloisField p e)) * rootSL2 .E8 (GaloisField p e) thetaE8 B =
          rootSL2 .E8 (GaloisField p e) thetaE8 B * (c : ModGL .E8 (GaloisField p e)) :=
      fun B => by
        have hB : (⟨rootSL2 .E8 (GaloisField p e) thetaE8 B, rootSL2_mem_adjointGroup _ _⟩ :
            ↥(adjointGroup .E8 (GaloisField p e))) ∈ stdRankOne (e8Datum (GaloisField p e))
              thetaE8 := (mem_stdRankOne_e8_iff _).2 ⟨B, rfl⟩
        exact congrArg Subtype.val (hcR _ hB)
    have hcL := mem_parabolicLevi_of_commute_rootSL2_E8 hK c.2 hcom
    have hgc : (g : ModGL .E8 (GaloisField p e)) *
        rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : (GaloisField p e)ˣ)) *
          (g : ModGL .E8 (GaloisField p e))⁻¹ = (c : ModGL .E8 (GaloisField p e)) := by
      rw [← hzd]
      exact (congrArg Subtype.val hcg).symm
    have hc2' : (c : ModGL .E8 (GaloisField p e)) * (c : ModGL .E8 (GaloisField p e)) = 1 :=
      congrArg Subtype.val hc2
    rcases exists_rational_conj_e8 hKodd c.2 g.2 hc2' hcL (hcom (uSL 1)) hgc with
      hd | ⟨δ, hδ, u, hu, hu1, hu2⟩
    · refine ⟨1, fun z' _ _ => by simp, ?_⟩
      simpa using mem_excSignGroup_e8 thetaE8 hd
    · refine ⟨⟨u, hu⟩, fun z' hz' hz'c => ?_, ?_⟩
      · rcases central_stdRankOne_e8 hK hz' hz'c with h1 | h1
        · rw [show z' = 1 from Subtype.ext h1]
          simp
        · refine Subtype.ext ?_
          change u * (z' : ModGL .E8 (GaloisField p e)) = (z' : ModGL .E8 (GaloisField p e)) * u
          rw [h1]
          exact hu2
      · exact mem_excSignGroup_e8 δ hu1

theorem pairFrame_e8 (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E8 0 p e) :
    PairFrame (excSignGroup .E8 p e)
      (fundamentalSubgroups .E8 (Generic.modelUniv .E8 0 p e Fact.out).D) := by
  have hsingle : Generic.FundamentalSingleClass .E8 (Generic.modelUniv .E8 0 p e Fact.out).D :=
    fundamentalSingleClass .E8 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hlong : ∀ k : Fin (Generic.modelUniv .E8 0 p e Fact.out).D.rank,
      Generic.IsLongestRoot (Generic.modelUniv .E8 0 p e Fact.out).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .E8 0 p e Fact.out trivial hadm k trivial
  have hθ : Generic.IsLongestRoot (Generic.modelUniv .E8 0 p e Fact.out).D thetaE8 :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl hlong
      (mem_adjDatum_roots.2 isRoot_thetaE8)
  exact pairFrame_of_centralizer (Generic.modelUniv .E8 0 p e Fact.out).D
    (excSignGroup .E8 p e) thetaE8 hθ hsingle (hZ_e8 hp2) (hbase_e8 hp2)

end Model

end CFSG.ClassicalInvolution.ModelFacts
