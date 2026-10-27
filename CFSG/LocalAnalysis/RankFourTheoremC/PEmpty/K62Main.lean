module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62Lift
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62Coord
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Facts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp)
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane IsMaxTwoInvariantIn)

structure BetaStructure (p : ℕ) (X : Type) [Group X] [Finite X] (P : Sylow p X) (x z : X) :
    Prop where
  card_components : Nat.card (ComponentIndex (X ⧸ primeComplementCore (G := X) p)) = p
  centreless : ∀ C : ComponentIndex (X ⧸ primeComplementCore (G := X) p), Subgroup.center C.1 = ⊥
  transitive : ∀ C C' : ComponentIndex (X ⧸ primeComplementCore (G := X) p),
    ∃ k : ℕ, cjComp ((x : X ⧸ primeComplementCore (G := X) p) ^ k) C = C'
  z_mem_layer : (z : X ⧸ primeComplementCore (G := X) p) ∈
    layer (X ⧸ primeComplementCore (G := X) p)
  pRank_le : Open.pRank p (P : Subgroup X) ≤ p

@[expose] def KFactBetaStructure : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X] [Finite X] (P : Sylow p X) (x z : X), Plane63 p X P x z →
    (∃ L K : Subgroup (X ⧸ primeComplementCore (G := X) p),
      IsComponentOf L ⊤ ∧ IsComponentOf K ⊤ ∧ L ≠ K) →
    BetaStructure p X P x z

theorem kFactMultiComponent_of_beta (hβ : KFactBetaStructure) : KFactMultiComponent := by
  intro p X _ _ P x z hpl hcomp T hT
  have hβs := hβ p X P x z hpl hcomp
  have hp := hpl.prime
  have hp2 : p ≠ 2 := by have := hpl.five_le; omega
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  have hD3 : ¬ p ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp (primeComplementCore_coprime p)
  have hB : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup X) :=
    IsPGroup.of_card (n := 2) hpl.plane.card_eq
  have hxB : x ∈ (zpowers x ⊔ zpowers z : Subgroup X) := Subgroup.mem_sup_left (mem_zpowers x)
  have hzB : z ∈ (zpowers x ⊔ zpowers z : Subgroup X) := Subgroup.mem_sup_right (mem_zpowers z)
  have hxp : x ^ p = 1 := hpl.plane.isElemAbelian.2 x hxB
  have hzp : z ^ p = 1 := hpl.plane.isElemAbelian.2 z hzB
  have hxz : x * z = z * x := by
    have := hpl.plane.isElemAbelian.1.is_comm.comm (⟨x, hxB⟩ : ↥(zpowers x ⊔ zpowers z))
      ⟨z, hzB⟩
    exact congrArg Subtype.val this
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : (zpowers x ⊔ zpowers z : Subgroup X) = zpowers x := by
      rw [h, zpowers_one_eq_bot, sup_bot_eq]
    have h2 : Nat.card (zpowers x) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hxp)
    have h3 := hpl.plane.card_eq
    rw [h1] at h3
    have h4 : p ^ 2 ≤ p := h3 ▸ h2
    have h5 : 1 < p := hp.one_lt
    nlinarith
  have hzb1 : (z : X ⧸ D) ≠ 1 := by
    intro h
    have hzD : z ∈ D := (QuotientGroup.eq_one_iff z).mp h
    have hord : orderOf z = p := orderOf_eq_prime hzp hz1
    apply hD3
    rw [← hord, ← Subgroup.orderOf_mk z hzD]
    exact orderOf_dvd_natCard _
  have hxzb : (x : X ⧸ D) * (z : X ⧸ D) = (z : X ⧸ D) * (x : X ⧸ D) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxz]
  have hzpb : (z : X ⧸ D) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hzp, QuotientGroup.mk_one]
  have hT' := K62.isMaxTwoInvariantIn_map hp hp2 hD3 hB hT
  have hBmap : (zpowers x ⊔ zpowers z : Subgroup X).map (QuotientGroup.mk' D) =
      zpowers (x : X ⧸ D) ⊔ zpowers (z : X ⧸ D) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  rw [hBmap] at hT'
  have hZ := hβs.centreless
  have hzL := hβs.z_mem_layer
  have hne := K62.π_ne_one hZ hxzb hzb1 hzL hβs.transitive
  have hN := K62.zcoord_mem_normalizer hZ hp hp2 hxzb hzL hβs.card_components hβs.transitive hT'
  obtain ⟨W, hWe, hWc, hWT⟩ := K62.exists_elemAbelian_of_coords hZ hp hzpb hzL hne hN
  rw [hβs.card_components] at hWc
  have hk := K62.le_pRank_normalizer hp hp2 hD3 hB hT hWe hWc hWT
  exact hβs.pRank_le.trans hk

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
