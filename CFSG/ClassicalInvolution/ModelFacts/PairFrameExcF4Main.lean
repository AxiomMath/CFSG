module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Rational
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcSigns
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcReduce
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalF4

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank

section StdRankOne

variable {K : Type} [Field K]

theorem mem_stdRankOne_f4_iff (r : ↥(adjointGroup .F4 K)) :
    r ∈ stdRankOne (f4Datum K) thetaF4 ↔
      ∃ A : SL2 K, (r : ModGL .F4 K) = rootSL2 .F4 K thetaF4 A := by
  have hb := subgroupOf_rootSubgroup_sup_eq (K := K) (rootOperatorFamily .F4) isRoot_thetaF4
  have hL := (exceptional_Lang_root_rank_one_torus_transport .F4 K isRoot_thetaF4).1
  change r ∈ rootGroup (rootOperatorFamily .F4) K thetaF4 ⊔
    rootGroup (rootOperatorFamily .F4) K (-thetaF4) ↔ _
  rw [← hb, Subgroup.mem_subgroupOf, ← hL, rootRankOneGroup, MonoidHom.mem_range]
  exact exists_congr fun A => eq_comm

theorem central_stdRankOne_f4 (hK : ringChar K ≠ 2) {z : ↥(adjointGroup .F4 K)}
    (hz : z ∈ stdRankOne (f4Datum K) thetaF4)
    (hzc : ∀ r ∈ stdRankOne (f4Datum K) thetaF4, z * r = r * z) :
    (z : ModGL .F4 K) = 1 ∨
      (z : ModGL .F4 K) = rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : Kˣ)) := by
  obtain ⟨A, hA⟩ := (mem_stdRankOne_f4_iff z).1 hz
  have hinj : Function.Injective (rootSL2 .F4 K thetaF4) :=
    ((exceptional_Lang_root_rank_one_data .F4 K thetaF4).2.2.2.2.2.2.2.1 hK).1
  have hcomm : ∀ B : SL2 K, A * B = B * A := fun B => by
    apply hinj
    have hB : (⟨rootSL2 .F4 K thetaF4 B, rootSL2_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) ∈
        stdRankOne (f4Datum K) thetaF4 := (mem_stdRankOne_f4_iff _).2 ⟨B, rfl⟩
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
    exact rootTorusSL2_thetaF4 (-1)

end StdRankOne

section Model

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

theorem odd_natCard_galoisField_f4 (hp2 : p ≠ 2) : Odd (Nat.card (GaloisField p e)) := by
  rw [GaloisField.card p e (NeZero.ne e)]
  exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow

theorem rootDiagUnit_corootDiagF4_mul_self {F : Type} [Field F] (δ : Fin (Tag.rank .F4) → ℤ) :
    rootDiagUnit .F4 (corootDiagF4 δ (-1 : Fˣ)) *
      rootDiagUnit .F4 (corootDiagF4 δ (-1 : Fˣ)) = 1 := by
  rw [← rootDiagUnit_mul, ← rootDiagUnit_one]
  congr 1
  funext i
  rcases corootDiagF4_neg_one_sign (F := F) δ i with h | h <;> simp [h]

theorem mem_excSignGroup_f4 {u : ↥(adjointGroup .F4 (GaloisField p e))} (δ : Fin (Tag.rank .F4) → ℤ)
    (hu : (u : ModGL .F4 (GaloisField p e)) =
      rootDiagUnit .F4 (corootDiagF4 δ (-1 : (GaloisField p e)ˣ))) : u ∈ excSignGroup .F4 p e :=
  mem_excSignGroup.2 ⟨corootDiagF4 δ (-1), corootDiagF4_neg_one_sign δ, hu⟩

theorem hZ_f4 (hp2 : p ≠ 2) :
    ∀ c ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4,
      (∀ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4, c * r = r * c) →
        c ∈ excSignGroup .F4 p e ∧ c * c = 1 := by
  intro c hc hcc
  rcases central_stdRankOne_f4 (ringChar_galoisField_ne_two hp2) hc hcc with h | h
  · have h1 : c = 1 := Subtype.ext h
    rw [h1]
    exact ⟨one_mem _, mul_one _⟩
  · refine ⟨mem_excSignGroup_f4 thetaF4 h, Subtype.ext ?_⟩
    change (c : ModGL .F4 (GaloisField p e)) * (c : ModGL .F4 (GaloisField p e)) = 1
    rw [h]
    exact rootDiagUnit_corootDiagF4_mul_self thetaF4

theorem hbase_f4 (hp2 : p ≠ 2) :
    ∀ c : ↥(adjointGroup .F4 (GaloisField p e)),
      (∀ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4, c * r = r * c) → c * c = 1 →
      (∃ g z : ↥(adjointGroup .F4 (GaloisField p e)),
        z ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4 ∧
        (∀ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4, z * r = r * z) ∧
        c = g * z * g⁻¹) →
      ∃ x : ↥(adjointGroup .F4 (GaloisField p e)),
        (∀ z ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4,
          (∀ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4, z * r = r * z) →
            x * z = z * x) ∧
        x * c * x⁻¹ ∈ excSignGroup .F4 p e := by
  intro c hcR hc2 ⟨g, z, hz, hzc, hcg⟩
  have hK : ringChar (GaloisField p e) ≠ 2 := ringChar_galoisField_ne_two hp2
  have hKodd := odd_natCard_galoisField_f4 (p := p) (e := e) hp2
  rcases central_stdRankOne_f4 hK hz hzc with hz1 | hzd
  ·
    have hc1 : c = 1 := by
      rw [hcg, show z = 1 from Subtype.ext hz1]
      group
    refine ⟨1, fun z' _ _ => by simp, ?_⟩
    rw [hc1, one_mul, inv_one, mul_one]
    exact one_mem _
  · have hcom : ∀ B : SL2 (GaloisField p e),
        (c : ModGL .F4 (GaloisField p e)) * rootSL2 .F4 (GaloisField p e) thetaF4 B =
          rootSL2 .F4 (GaloisField p e) thetaF4 B * (c : ModGL .F4 (GaloisField p e)) :=
      fun B => by
        have hB : (⟨rootSL2 .F4 (GaloisField p e) thetaF4 B, rootSL2_mem_adjointGroup _ _⟩ :
            ↥(adjointGroup .F4 (GaloisField p e))) ∈ stdRankOne (f4Datum (GaloisField p e))
              thetaF4 := (mem_stdRankOne_f4_iff _).2 ⟨B, rfl⟩
        exact congrArg Subtype.val (hcR _ hB)
    have hcL := mem_parabolicLevi_of_commute_rootSL2_F4 hK c.2 hcom
    have hgc : (g : ModGL .F4 (GaloisField p e)) *
        rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : (GaloisField p e)ˣ)) *
          (g : ModGL .F4 (GaloisField p e))⁻¹ = (c : ModGL .F4 (GaloisField p e)) := by
      rw [← hzd]
      exact (congrArg Subtype.val hcg).symm
    have hc2' : (c : ModGL .F4 (GaloisField p e)) * (c : ModGL .F4 (GaloisField p e)) = 1 :=
      congrArg Subtype.val hc2
    rcases exists_rational_conj_f4 hKodd c.2 g.2 hc2' hcL (hcom (uSL 1)) hgc with
      hd | ⟨δ, hδ, -, u, hu, hu1, hu2⟩
    · refine ⟨1, fun z' _ _ => by simp, ?_⟩
      simpa using mem_excSignGroup_f4 thetaF4 hd
    · refine ⟨⟨u, hu⟩, fun z' hz' hz'c => ?_, ?_⟩
      · rcases central_stdRankOne_f4 hK hz' hz'c with h1 | h1
        · rw [show z' = 1 from Subtype.ext h1]
          simp
        · refine Subtype.ext ?_
          change u * (z' : ModGL .F4 (GaloisField p e)) = (z' : ModGL .F4 (GaloisField p e)) * u
          rw [h1]
          exact hu2
      · exact mem_excSignGroup_f4 δ hu1

theorem pairFrame_f4 (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .F4 0 p e) :
    PairFrame (excSignGroup .F4 p e)
      (fundamentalSubgroups .F4 (Generic.modelUniv .F4 0 p e Fact.out).D) := by
  have hsingle : Generic.FundamentalSingleClass .F4 (Generic.modelUniv .F4 0 p e Fact.out).D :=
    fundamentalSingleClass .F4 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθ : Generic.IsLongestRoot (Generic.modelUniv .F4 0 p e Fact.out).D thetaF4 :=
    isLongestRoot_f4Datum_of_iform_eq_four isRoot_thetaF4 iform_thetaF4_self
  exact pairFrame_of_centralizer (Generic.modelUniv .F4 0 p e Fact.out).D
    (excSignGroup .F4 p e) thetaF4 hθ hsingle (hZ_f4 hp2) (hbase_f4 hp2)

end Model

end CFSG.ClassicalInvolution.ModelFacts
