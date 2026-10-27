module

public import CFSG.GH74.SectionalRankExtension
public import CFSG.RankThree.PartOne.S11c.G2Transport

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GH74 CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley

open scoped MatrixGroups

variable {K : Type} [Field K]

private def finTwoArrowMulEquiv (G : Type*) [Group G] : (Fin 2 → G) ≃* G × G where
  toFun t := (t 0, t 1)
  invFun p := ![p.1, p.2]
  left_inv t := by funext i; fin_cases i <;> rfl
  right_inv p := rfl
  map_mul' _ _ := rfl

theorem sectionalTwoRankLE_rootSpan
    [Finite K] (hK : Odd (Nat.card K))
    {a : Fin Tag.G2.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) (ha1 : a ≠ 1) :
    SectionalTwoRankLE (rootSpan .G2 K (rootCharKernel a)) 4 := by
  classical
  obtain ⟨α, β, h, hS⟩ := CFSG.RankThree.PartOne.exists_g2_pair hK ha ha1
  have h2 : (2 : K) ≠ 0 :=
    Ring.two_ne_zero (CFSG.RankThree.PartOne.ringChar_ne_two_of_odd_card hK)
  have hSL : SectionalTwoRankLE (SL2 K × SL2 K) 4 := by
    have h := SectionalTwoRankLE.prod (SectionalTwoRankLE.specialLinearGroup K h2)
      (SectionalTwoRankLE.specialLinearGroup K h2)
    simpa [SL2] using h
  haveI : Finite (SL2 K × SL2 K) := inferInstance
  let f : SL2 K × SL2 K →* ↥(CFSG.RankThree.PartOne.g2Mul h K).range :=
    (CFSG.RankThree.PartOne.g2Mul h K).codRestrict (CFSG.RankThree.PartOne.g2Mul h K).range fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
    exact ⟨x, Subtype.ext hx⟩
  have hrange : SectionalTwoRankLE ↥(CFSG.RankThree.PartOne.g2Mul h K).range 4 :=
    SectionalTwoRankLE.of_surjective f hf hSL
  exact SectionalTwoRankLE.of_mulEquiv (MulEquiv.subgroupCongr hS) hrange

theorem sectionalTwoRankLE_toralCentralizer
    [Finite K]
    (hK : Odd (Nat.card K)) {a : Fin Tag.G2.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) (ha1 : a ≠ 1) :
    SectionalTwoRankLE (toralCentralizer .G2 K a) 6 := by
  classical
  set X : Subgroup (ModGL .G2 K) := toralCentralizer .G2 K a with hX
  set S : Subgroup (ModGL .G2 K) := rootSpan .G2 K (rootCharKernel a) with hS
  set T : Subgroup (ModGL .G2 K) := torusGroup .G2 K with hT
  have hSle : S ≤ X := rootSpan_rootCharKernel_le_toralCentralizer a
  have hTle : T ≤ X := torusGroup_le_toralCentralizer a
  haveI : (S.subgroupOf X).Normal := rootSpan_rootCharKernel_normal a
  have hS4 : SectionalTwoRankLE S 4 := sectionalTwoRankLE_rootSpan hK ha ha1
  have hN4 : SectionalTwoRankLE (S.subgroupOf X) 4 :=
    SectionalTwoRankLE.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSle).symm hS4
  have hT2 : SectionalTwoRankLE T 2 := by
    have hfin : SectionalTwoRankLE (Fin 2 → Kˣ) 2 := by
      have h := SectionalTwoRankLE.prod (SectionalTwoRankLE.units K) (SectionalTwoRankLE.units K)
      exact SectionalTwoRankLE.of_mulEquiv (finTwoArrowMulEquiv Kˣ).symm (by simpa using h)
    obtain ⟨e, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
    exact SectionalTwoRankLE.of_mulEquiv e hfin
  have hQ2 : SectionalTwoRankLE (X ⧸ S.subgroupOf X) 2 := by
    refine SectionalTwoRankLE.quotient_of_sup_eq_top (S.subgroupOf X)
      (SectionalTwoRankLE.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTle).symm hT2) ?_
    have hEq : X = T ⊔ S := by
      rw [hX, hT, hS]
      exact le_antisymm (fun g hg => CFSG.RankThree.PartOne.toralCentralizer_G2_le
        (CFSG.RankThree.PartOne.ringChar_ne_two_of_odd_card hK) ha hg) (toralRootGroup_le a)
    rw [← Subgroup.subgroupOf_sup hTle hSle, ← hEq, Subgroup.subgroupOf_self]
  exact SectionalTwoRankLE.of_normal (S.subgroupOf X) hN4 hQ2

theorem sectionalTwoRankLE_adjointGroup_G2
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) :
    SectionalTwoRankLE (adjointGroup .G2 K) 8 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP
  by_cases hbot : P = ⊥
  · subst hbot
    exact ⟨∅, by simp, by simp⟩
  ·
    haveI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hbot
    have hCenter : IsPGroup 2 (Subgroup.center P) := hP.to_subgroup (Subgroup.center P)
    have hCenterNt : Nontrivial (Subgroup.center P) := IsPGroup.center_nontrivial hP
    obtain ⟨n, hn0, hn⟩ := (IsPGroup.nontrivial_iff_card hCenter).mp hCenterNt
    have hdiv : 2 ∣ Nat.card (Subgroup.center P) := by
      rw [hn]
      exact dvd_pow_self 2 (ne_of_gt hn0)
    obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2 hdiv
    set t : ModGL .G2 K := (z0 : ModGL .G2 K) with ht_def
    have ht_mem : t ∈ adjointGroup .G2 K := by
      simpa [ht_def] using (z0 : P).2
    have ht2 : t ^ 2 = 1 := by
      have h : z0 ^ 2 = 1 := by rw [← hz0]; exact pow_orderOf_eq_one z0
      have hmap := congrArg (fun w : Subgroup.center P => (w : ModGL .G2 K)) h
      simpa using hmap
    have ht1 : t ≠ 1 := by
      intro h
      have hz : z0 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        simpa [ht_def] using h
      rw [hz] at hz0
      simp at hz0
    obtain ⟨b, L, hLf, ψ, ι, hb, hb1, hψ, hι, himg, -⟩ :=
      CFSG.RankThree.PartOne.exists_involution_transport (K := K) hK ht_mem ht2 ht1
    letI : Field L := hLf
    have hZ6 : SectionalTwoRankLE (toralCentralizer .G2 K b) 6 :=
      sectionalTwoRankLE_toralCentralizer hK hb hb1
    set Y : Subgroup (ModGL .G2 K) := adjointGroup .G2 K ⊓ Subgroup.centralizer {t} with hY
    have hY8 : SectionalTwoRankLE Y 8 := by
      have eYZ : Y ≃* toralCentralizer .G2 K b :=
        (Subgroup.equivMapOfInjective Y ψ hψ).trans
          ((MulEquiv.subgroupCongr himg).trans
            (Subgroup.equivMapOfInjective (toralCentralizer .G2 K b) ι hι).symm)
      exact (SectionalTwoRankLE.of_mulEquiv eYZ.symm hZ6).mono (by norm_num)
    have hYA8 : SectionalTwoRankLE (Y.subgroupOf (adjointGroup .G2 K)) 8 :=
      SectionalTwoRankLE.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (show Y ≤ adjointGroup .G2 K from inf_le_left)).symm hY8
    have hPY : P ≤ Y.subgroupOf (adjointGroup .G2 K) := by
      intro p hp
      rw [Subgroup.mem_subgroupOf]
      refine ⟨p.2, ?_⟩
      change (p : ModGL .G2 K) ∈ Subgroup.centralizer ({t} : Set (ModGL .G2 K))
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : (⟨p, hp⟩ : P) * z0 = z0 * (⟨p, hp⟩ : P) :=
        Subgroup.mem_center_iff.1 z0.2 (⟨p, hp⟩ : P)
      have hmap := congrArg (fun w : P => (w : ModGL .G2 K)) hcomm
      simpa [ht_def] using hmap
    obtain ⟨s, hs, hsP⟩ := hYA8 (P.subgroupOf (Y.subgroupOf (adjointGroup .G2 K)))
      hP.comap_subtype
    refine ⟨s.image (Subgroup.subtype (Y.subgroupOf (adjointGroup .G2 K))),
      Finset.card_image_le.trans hs, ?_⟩
    rw [Finset.coe_image, ← MonoidHom.map_closure, hsP,
      Subgroup.map_subgroupOf_eq_of_le hPY]

theorem sectionalTwoRankLE_of_chevalleyExceptionalModel_G2
    {S : Type} [Group S] {p f : ℕ} (hp2 : p ≠ 2)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel S .G2 p f) :
    SectionalTwoRankLE S 8 := by
  obtain ⟨hadm, hun⟩ := h
  obtain ⟨K, hfield, hfin, hcard, ⟨e⟩⟩ := hun
  letI : Field K := hfield
  letI : Finite K := hfin
  have hodd : Odd (Nat.card K) := by
    rw [hcard]
    exact (hadm.1.odd_of_ne_two hp2).pow
  have hA : SectionalTwoRankLE (adjointGroup .G2 K) 8 :=
    sectionalTwoRankLE_adjointGroup_G2 hodd
  have hAQ : SectionalTwoRankLE (AdjointQuotient .G2 K) 8 :=
    SectionalTwoRankLE.quotient (Subgroup.center ↥(adjointGroup .G2 K)) hA
  exact SectionalTwoRankLE.of_mulEquiv e.symm hAQ

end CFSG.LieType.Chevalley

end
