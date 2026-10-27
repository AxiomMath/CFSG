module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Helpers

theorem t263_isComponentOf_of_core_bot {G : Type*} [Group G] {p : ℕ} {X L : Subgroup G}
    (hX : GLAPPrimeCoreOf p X = ⊥) (hL : GLAPComponent p X L) : IsComponentOf L X := by
  have hcore : GLAPPrimeCore p ↥X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hX
  refine ⟨hL.1, hL.2.1, ?_⟩
  have hq := hL.2.2.1.2.2
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective (L.subgroupOf X) _ hinj).symm.trans
      (Subgroup.subgroupOfEquivOfLe hL.1)) hq

theorem t263_pSimple_map_nonempty {G G' : Type} [Group G] [Group G'] [Finite G] {p : ℕ} (hp : p.Prime)
    (ψ : G →* G') (A : Subgroup G) (hker : Nat.Coprime p (Nat.card ↥(A ⊓ ψ.ker))) :
    Nonempty (PSimple p A ≃* PSimple p (A.map ψ)) :=
  ⟨QuotientGroup.congr _ _ (lcEquiv hp ψ A hker) (Subgroup.map_center_eq _)⟩

theorem t263_pSimple_core_bot_nonempty {G : Type} [Group G] {p : ℕ} {L : Subgroup G}
    (hcore : GLAPPrimeCore p ↥L = ⊥) : Nonempty (PSimple p L ≃* (↥L ⧸ Subgroup.center ↥L)) := by
  let e0 : PQuot p L ≃* ↥L := (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact ⟨QuotientGroup.congr (Subgroup.center (PQuot p L)) (Subgroup.center ↥L) e0 (Subgroup.map_center_eq e0)⟩

theorem t263_eq_one_of_pow_pow {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G} {a k : ℕ}
    (h1 : x ^ (p ^ a) = 1) (h2 : x ^ (2 ^ k) = 1) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (p ^ a) :=
    Nat.Coprime.pow k a ((Nat.coprime_primes Nat.prime_two hp).2 hp2.symm)
  have := pow_gcd_eq_one.2 ⟨h2, h1⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem t263_sylow_map_eq {A A' : Type*} [Group A] [Group A'] [Finite A] (f : A →* A') (P : Subgroup A)
    (hV : IsPGroup 2 ↥(P.map f)) (Q : Sylow 2 ↥P) :
    ((Q : Subgroup ↥P).map P.subtype).map f = P.map f := by
  have hsurj : Function.Surjective (f.subgroupMap P) := f.subgroupMap_surjective P
  have htop : IsPGroup 2 ↥(⊤ : Subgroup ↥(P.map f)) := hV.of_equiv Subgroup.topEquiv.symm
  have h1 : (⊤ : Subgroup ↥(P.map f)) = ((Q.mapSurjective hsurj : Sylow 2 ↥(P.map f)) : Subgroup ↥(P.map f)) :=
    (Q.mapSurjective hsurj).is_maximal' htop le_top
  rw [Sylow.coe_mapSurjective hsurj Q] at h1
  apply le_antisymm
  · exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  · rintro _ ⟨x, hxP, rfl⟩
    have hx : (⟨f x, ⟨x, hxP, rfl⟩⟩ : ↥(P.map f)) ∈ (⊤ : Subgroup ↥(P.map f)) := trivial
    rw [h1] at hx
    obtain ⟨q, hq, hqe⟩ := hx
    refine ⟨(q : A), ⟨q, hq, rfl⟩, ?_⟩
    have := congrArg Subtype.val hqe
    exact this

end Helpers

end CFSG.LocalAnalysis.GLTheoremA.T263

end
